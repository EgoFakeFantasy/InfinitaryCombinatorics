$ErrorActionPreference = 'Stop'
$dpRoot = Join-Path $PSScriptRoot '.lake/packages/YesMetaZFC'
$dpManifest = Get-Content -Raw (Join-Path $PSScriptRoot 'dependency-patches/manifest.json') | ConvertFrom-Json
$dpFile = Join-Path $dpRoot $dpManifest.path
$dpPatch = Join-Path $PSScriptRoot 'dependency-patches/kernel-checked-axioms.patch'
$dpRevision = (& git -C $dpRoot rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $dpRevision -ne $dpManifest.revision) { throw 'Unexpected YesMetaZFC revision' }
if ((Get-FileHash $dpPatch -Algorithm SHA256).Hash.ToLowerInvariant() -ne $dpManifest.patch_sha256) { throw 'Dependency patch hash mismatch' }
function Get-NormalizedDependencyHash {
  $dpNormalized = [IO.File]::ReadAllText($dpFile).Replace("`r`n", "`n")
  [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData([Text.Encoding]::UTF8.GetBytes($dpNormalized))).ToLowerInvariant()
}
$dpHash = Get-NormalizedDependencyHash
if ($dpHash -eq $dpManifest.original_normalized_sha256) {
  & git -C $dpRoot apply --check -- $dpPatch
  if ($LASTEXITCODE -ne 0) { throw 'Dependency patch does not apply cleanly' }
  & git -C $dpRoot apply -- $dpPatch
  if ($LASTEXITCODE -ne 0) { throw 'Dependency patch failed' }
} elseif ($dpHash -ne $dpManifest.patched_sha256) {
  throw 'Unrecognized local edits in upstream Axioms/Common.lean; refusing to overwrite'
}
if ((Get-NormalizedDependencyHash) -ne $dpManifest.patched_sha256) { throw 'Patched dependency hash mismatch' }
$dpNormalized = [IO.File]::ReadAllText($dpFile).Replace("`r`n", "`n")
if ((Get-FileHash $dpFile -Algorithm SHA256).Hash.ToLowerInvariant() -ne $dpManifest.patched_sha256) {
  [IO.File]::WriteAllText($dpFile, $dpNormalized, [Text.UTF8Encoding]::new($false))
}
Write-Output 'Verified pinned YesMetaZFC kernel-certificate patch.'
