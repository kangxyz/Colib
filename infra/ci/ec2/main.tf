data "aws_caller_identity" "current" {}

data "aws_availability_zones" "available" {
  state = "available"
  filter {
    name   = "opt-in-status"
    values = ["opt-in-not-required"]
  }
}

locals {
  app_key_name         = var.github_app_key_ssm_name
  webhook_name         = "/${var.prefix}/app/webhook-secret"
  parameter_arn_prefix = "arn:aws:ssm:${var.aws_region}:${var.aws_account_id}:parameter"
}

# An isolated public subnet avoids a permanently billed NAT gateway.
# The module's runner security group has no inbound rules.
resource "aws_vpc" "runner" {
  cidr_block           = "10.85.0.0/16"
  enable_dns_support   = true
  enable_dns_hostnames = true
}

resource "aws_internet_gateway" "runner" {
  vpc_id = aws_vpc.runner.id
}

resource "aws_subnet" "runner" {
  vpc_id                  = aws_vpc.runner.id
  cidr_block              = "10.85.1.0/24"
  availability_zone       = data.aws_availability_zones.available.names[0]
  map_public_ip_on_launch = true
}

resource "aws_route_table" "runner" {
  vpc_id = aws_vpc.runner.id
  route {
    cidr_block = "0.0.0.0/0"
    gateway_id = aws_internet_gateway.runner.id
  }
}

resource "aws_route_table_association" "runner" {
  subnet_id      = aws_subnet.runner.id
  route_table_id = aws_route_table.runner.id
}

module "runners" {
  source  = "github-aws-runners/github-runner/aws"
  version = "8.0.0"

  aws_region = var.aws_region
  prefix     = var.prefix
  vpc_id     = aws_vpc.runner.id
  subnet_ids = [aws_subnet.runner.id]

  # Secrets are created outside Terraform; only names and ARNs enter state.
  github_app = {
    id = var.github_app_id
    key_base64_ssm = {
      name = local.app_key_name
      arn  = "${local.parameter_arn_prefix}${local.app_key_name}"
    }
    webhook_secret_ssm = {
      name = local.webhook_name
      arn  = "${local.parameter_arn_prefix}${local.webhook_name}"
    }
  }

  enable_organization_runners             = false
  repository_white_list                   = ["kangxyz/colib"]
  runner_extra_labels                     = ["colib-ec2"]
  enable_runner_bidirectional_label_match = true
  enable_dynamic_labels                   = false

  # One repository and one runner lane do not need a separate event bus/archive.
  eventbridge = { enable = false }

  enable_ephemeral_runners                = false
  enable_jit_config                       = false
  enable_job_queued_check                 = true
  runners_maximum_count                   = var.enabled ? 1 : 0
  scale_up_reserved_concurrent_executions = var.enabled ? 1 : 0
  state_event_rule_binaries_syncer        = var.enabled ? "ENABLED" : "DISABLED"
  idle_config                             = []
  pool_config                             = []
  instance_target_capacity_type           = "on-demand"
  instance_types                          = [var.instance_type]
  runner_architecture                     = "x64"
  runner_run_as                           = "ubuntu"
  runner_as_root                          = false
  associate_public_ipv4_address           = true
  minimum_running_time_in_minutes         = 10
  runner_boot_time_in_minutes             = 15
  scale_down_schedule_expression          = "cron(* * * * ? *)"
  scale_down_idle_confirmation_seconds    = 900
  job_retry                               = { enable = false }

  # The upstream default Linux bootstrap uses Amazon Linux/dnf.
  # Colib's existing native CI expects Ubuntu, Python >=3.11 and systemd.
  ami = {
    owners = ["099720109477"]
    filter = {
      name  = ["ubuntu/images/hvm-ssd-gp3/ubuntu-noble-24.04-amd64-server-*"]
      state = ["available"]
    }
  }
  userdata_template    = "${path.module}/ubuntu-user-data.sh.tftpl"
  userdata_pre_install = <<-SHELL
    systemd-run --unit=colib-ci-expiry --on-active=${var.runner_lifetime_minutes}m /sbin/shutdown -h now
  SHELL

  block_device_mappings = [{
    device_name           = "/dev/sda1"
    volume_size           = 200
    volume_type           = "gp3"
    encrypted             = true
    delete_on_termination = true
  }]
  runner_metadata_options = {
    http_endpoint               = "enabled"
    http_tokens                 = "required"
    http_put_response_hop_limit = 1
    instance_metadata_tags      = "enabled"
  }

  webhook_lambda_zip                = "${path.module}/lambdas/webhook.zip"
  runner_binaries_syncer_lambda_zip = "${path.module}/lambdas/runner-binaries-syncer.zip"
  runners_lambda_zip                = "${path.module}/lambdas/runners.zip"

  enable_ssm_on_runners                 = var.enable_ssm_debug_access
  enable_cloudwatch_agent               = true
  enable_user_data_debug_logging_runner = false
  logging_retention_in_days             = 7
  log_level                             = "info"

  depends_on = [aws_route_table_association.runner]
}
