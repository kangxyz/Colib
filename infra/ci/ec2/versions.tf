terraform {
  backend "s3" {}

  required_version = ">= 1.5.6, < 2.0"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = ">= 6.33, < 7.0"
    }
  }
}

provider "aws" {
  region              = var.aws_region
  allowed_account_ids = [var.aws_account_id]
  default_tags {
    tags = {
      Project   = "colib-ec2"
      ManagedBy = "Terraform"
    }
  }
}
