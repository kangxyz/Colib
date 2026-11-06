# Colib EC2 CI

This directory owns the repository-scoped, on-demand EC2 runner for `kangxyz/colib`.
It uses the same [upstream runner module, version 8.0.0](https://github.com/github-aws-runners/terraform-aws-github-runner/tree/v8.0.0)
and Ubuntu bootstrap pattern as Aglib. Colib has its own VPC, runner labels,
launch template, queues, Lambda functions, webhook secret and Terraform state.
Aglib's deployment is not changed. The existing GitHub App key is referenced from
SSM; its private key is not duplicated into this repository or Terraform state.

## Disabled deployment

The initial deployment on 2026-11-06 added 86 managed resources without updating
or deleting existing resources. Its encrypted, versioned state backend is
`colib-ec2-terraform-975049960217`, key `runner/terraform.tfstate`, in `us-east-1`.
The deployment is deliberately dormant:

| Control | Disabled value |
|---|---|
| Repository variable | `COLIB_SELF_HOSTED_ENABLED=false` |
| Terraform input | `enabled=false`, also the default |
| Scale-up Lambda reserved concurrency | `0` |
| Runner maximum | `0` |
| GitHub repository webhook | Inactive |
| Scheduled runner binary synchronization | Disabled |
| EC2 instances and registered Colib runners | None |

`COLIB_EC2_SHARED_HOST=true` prepares the current Aglib-style same-checkout
Build-to-Test handoff; it cannot admit an EC2 job while the separate self-hosted
gate is false. [Lean CI](../../../.github/LEAN_CI.md) owns the full optimized
hosted and self-hosted execution flow.

The repository variable gates both the caller and reusable workflow. Pushes and
manual dispatches continue to use GitHub-hosted Ubuntu. PRs and non-main revisions
use GitHub-hosted runners even after activation. The manual profile defaults to
`hosted`; choosing `ec2` while disabled still uses the hosted runner.

The deployment creates control infrastructure and a launch template, with no
EC2 instance resource or warm pool. Scheduled housekeeping and idle reclamation
remain available. Dormant control resources and stored objects can have small
AWS costs. An actual EC2 bootstrap/build trial has not been run while disabled.

## Runner configuration

The enabled configuration permits one `m7i.4xlarge` runner (16 vCPU, 64 GiB) in
`us-east-1`, with a 200 GiB encrypted gp3 root disk deleted on termination.
There is no NAT gateway or inbound security-group rule. IMDSv2 is required.
The autoscaler admits only `kangxyz/colib` and requires the exact cumulative labels
`self-hosted,linux,x64,colib-ec2`.

The persistent service has a 900-second idle confirmation and a 360-minute machine
watchdog. Build renews the watchdog using Aglib's timer restart pattern. Build and
Test limits are respectively 240 and 90 minutes on EC2. The root-owned
`/etc/colib-ci-runner-mode` marker identifies a Colib host. Colib and Stacks retain
their [independent cache boundaries](../../../docs/CACHING.md) on either runner
profile; this adapter does not introduce a shared cache containing both packages.

## Deployment inputs and state

Use Terraform 1.13.5 and the committed provider lock. Authenticate through AWS CLI
to the intended account, then configure the Terraform AWS provider for that CLI
profile. An AWS CLI login profile can be exposed to the provider through a local
`credential_process` that runs `aws configure export-credentials --format process`.
Keep that local AWS configuration outside Git.

Create these prerequisites before planning:

- A private, encrypted, versioned S3 state bucket, with public access blocked and
  S3 lockfiles enabled through `use_lockfile = true` in the backend configuration.
- An existing GitHub App key in a SecureString parameter named by
  `github_app_key_ssm_name`, stored as base64-encoded PEM as required by upstream.
- A separate random webhook secret in SecureString
  `/<prefix>/app/webhook-secret` (`/colib-ec2/app/webhook-secret` by default).
- A local variables file based on `terraform.tfvars.example`, with `enabled=false`.
  The AWS provider rejects an authenticated account different from `aws_account_id`.

Fetch the pinned Lambda archives and deploy the reviewed disabled plan:

```bash
bash fetch-lambdas.sh
terraform init -backend-config=/path/to/private/state.backend.hcl
terraform fmt -check
terraform validate
terraform plan -var-file=/path/to/private/deployment.tfvars.json -out=disabled.tfplan
terraform show disabled.tfplan
terraform apply disabled.tfplan
```

The initial plan has 86 managed creates, no updates/deletes and no EC2 instance.
The state backend, webhook secret and inactive GitHub hook are provisioned outside
that plan. Credentials, state, plans, variables and Lambda binaries are excluded
from Git. The binary archive digests are maintained in `lambdas.sha256`.

## Future activation

Activate only when requested. Keep the repository variable false while preparing:

1. Add `kangxyz/colib` to the existing GitHub App's selected repositories. The App
   needs repository Administration write, Actions read, Checks read and Metadata
   read, matching Aglib. The current CLI user token cannot change that App's
   repository selection (HTTP 403); this selection remains pending while dormant.
2. Apply a reviewed plan with `enabled=true`. It raises the runner maximum and
   reserved scale-up concurrency to one and enables binary synchronization.
3. Verify the runner distribution is available in the module's private S3 bucket.
   Configure the repository `workflow_job` hook with `terraform output -raw webhook_url`,
   the matching SSM webhook secret, JSON content type and SSL verification, then
   activate the hook. Keep the shared App-wide webhook settings unchanged.
4. Set `COLIB_SELF_HOSTED_ENABLED=true`. The manual EC2 probe with
   `verify-handoff=true` checks both jobs see the same runner/workspace. Dispatch
   the main-branch CI `ec2` profile and
   check the host marker, native checks, separate caches and idle termination.
   Only this trial establishes that the Colib runner actually works.

To suspend admission again, set the repository variable false, deactivate the
Colib hook, and apply `enabled=false`. Existing machines are reclaimed by idle
scale-down or the watchdog; changing these controls does not interrupt an active
machine immediately. Verify the Colib EC2 fleet and registered runners are empty.
