variable "enabled" {
  description = "Allow EC2 scale-up. Keep false until explicitly enabling self-hosted CI."
  type        = bool
  default     = false
}

variable "github_app_key_ssm_name" {
  description = "Existing GitHub App private-key SecureString. Only the parameter reference enters state."
  type        = string
}

variable "aws_region" {
  type    = string
  default = "us-east-1"
}

variable "aws_account_id" {
  description = "The account that may incur charges. Obtain it with aws sts get-caller-identity."
  type        = string
  validation {
    condition     = can(regex("^[0-9]{12}$", var.aws_account_id))
    error_message = "Set the intended 12-digit AWS account ID."
  }
}

variable "github_app_id" {
  description = "Numeric App ID, not Client ID. Its selected repositories must include kangxyz/colib before activation."
  type        = string
  validation {
    condition     = can(regex("^[0-9]+$", var.github_app_id))
    error_message = "Use the numeric GitHub App ID."
  }
}

variable "prefix" {
  type    = string
  default = "colib-ec2"
}

variable "instance_type" {
  type    = string
  default = "m7i.4xlarge"
  validation {
    condition     = contains(["m7i.4xlarge", "m7i.8xlarge"], var.instance_type)
    error_message = "The pilot permits only m7i.4xlarge or m7i.8xlarge."
  }
}

variable "runner_lifetime_minutes" {
  description = "Boot-to-termination watchdog; allow the full CI job and bootstrap margin."
  type        = number
  default     = 360
  validation {
    condition     = var.runner_lifetime_minutes >= 30 && var.runner_lifetime_minutes <= 480 && floor(var.runner_lifetime_minutes) == var.runner_lifetime_minutes
    error_message = "Use a whole number of minutes between 30 and 480."
  }
}

variable "enable_ssm_debug_access" {
  description = "Optional Session Manager permissions on runner instances."
  type        = bool
  default     = false
}
