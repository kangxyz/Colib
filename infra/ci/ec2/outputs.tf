output "webhook_url" {
  value = module.runners.webhook.endpoint
}

output "runner_launch_template_id" {
  value = module.runners.runners.launch_template_id
}

output "region" {
  value = var.aws_region
}

output "github_runner_labels" {
  value = ["self-hosted", "linux", "x64", "colib-ec2"]
}
