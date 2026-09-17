$ErrorActionPreference = 'Stop'
$icOriginalLocation = Get-Location
try {
  Set-Location -LiteralPath $PSScriptRoot
  New-Item -ItemType Directory -Path 'verification' -Force | Out-Null
  $icLibraryFiles = @('InfinitaryCombinatorics.lean', 'R0.lean') +
    @(Get-ChildItem -LiteralPath 'InfinitaryCombinatorics','R0' -Filter '*.lean' -Recurse |
      ForEach-Object { $_.FullName.Substring($PSScriptRoot.Length + 1).Replace('\','/') })
  $icFiles = $icLibraryFiles + @('Examples.lean','CheckR0.lean','Audit.lean')
  $icForbidden = '\b(sorry|admit|sorryAx|native_decide|unsafe)\b|(?m)^\s*(axiom|constant)\s'
  foreach ($icFile in $icFiles) {
    $icText = Get-Content -LiteralPath $icFile -Raw -Encoding utf8
    if ($icText -match $icForbidden) { throw "Forbidden construct in $icFile" }
    if ($icText -match '(?m)[ \t]+$|^(<<<<<<<|=======|>>>>>>>)') {
      throw "Whitespace or merge marker in $icFile"
    }
  }
  $icInitialHashes = @{}
  foreach ($icFile in $icFiles) {
    $icInitialHashes[$icFile] = (Get-FileHash -LiteralPath $icFile -Algorithm SHA256).Hash
  }
  # Fail when a new mathematical module is omitted from the umbrella import and audit.
  $icModules = @{}
  foreach ($icFile in $icLibraryFiles) {
    $icModules[$icFile.Replace('/','.').Replace('.lean','')] = $icFile
  }
  $icQueue = [Collections.Generic.Queue[string]]::new()
  $icSeen = [Collections.Generic.HashSet[string]]::new()
  $icQueue.Enqueue('InfinitaryCombinatorics')
  while ($icQueue.Count -gt 0) {
    $icModule = $icQueue.Dequeue()
    if (-not $icSeen.Add($icModule)) { continue }
    $icText = Get-Content -LiteralPath $icModules[$icModule] -Raw
    foreach ($icMatch in [regex]::Matches($icText, '(?m)^import\s+([A-Za-z0-9_.]+)\s*$')) {
      $icImport = $icMatch.Groups[1].Value
      if ($icModules.ContainsKey($icImport)) { $icQueue.Enqueue($icImport) }
    }
  }
  foreach ($icModule in $icModules.Keys) {
    if (-not $icSeen.Contains($icModule)) { throw "Unaudited module: $icModule" }
  }
  $icSnapshot = Get-Content -LiteralPath 'docs/r0-source-hashes.json' -Raw | ConvertFrom-Json
  foreach ($icSource in $icSnapshot) {
    $icHash = (Get-FileHash -LiteralPath $icSource.path -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($icHash -ne $icSource.sha256) { throw "Bundled R0 changed: $($icSource.path)" }
  }
  & lake build 2>&1 | Tee-Object -FilePath 'verification/build.log'
  if ($LASTEXITCODE -ne 0) { throw 'Library build failed' }
  & lake env lean Examples.lean 2>&1 | Tee-Object -FilePath 'verification/examples.log'
  if ($LASTEXITCODE -ne 0) { throw 'Consumer examples failed' }
  & lake env lean CheckR0.lean 2>&1 | Tee-Object -FilePath 'verification/r0-statements.log'
  if ($LASTEXITCODE -ne 0) { throw 'Unfolded R0 statements failed' }
  & lake env lean Audit.lean 2>&1 | Tee-Object -FilePath 'verification/axiom-audit.log'
  if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed' }
  $icAudit = Get-Content -LiteralPath 'verification/axiom-audit.log' -Raw
  if ($icAudit -notmatch 'Kernel audit passed: (\d+) declarations, (\d+) theorem constants') {
    throw 'Missing successful audit summary'
  }
  $icDeclarations = [int]$Matches[1]
  $icTheorems = [int]$Matches[2]
  $icManifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
  foreach ($icFile in $icFiles) {
    if ((Get-FileHash -LiteralPath $icFile -Algorithm SHA256).Hash -ne $icInitialHashes[$icFile]) {
      throw "Source changed during verification; rerun: $icFile"
    }
  }
  $icFinalLibraryCount = 2 + @(Get-ChildItem -LiteralPath 'InfinitaryCombinatorics','R0' -Filter '*.lean' -Recurse).Count
  if ($icFinalLibraryCount -ne $icLibraryFiles.Count) { throw 'Module set changed during verification' }
  $icReport = [ordered]@{
    checked_at_utc = [DateTime]::UtcNow.ToString('o')
    lean_toolchain = (Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim()
    mathlib_revision = ($icManifest.packages | Where-Object name -eq 'mathlib').rev
    build = 'passed'
    consumer_examples = 'passed'
    unfolded_R0_statements = 'passed'
    axiom_audit = 'passed'
    declarations = $icDeclarations
    theorem_constants = $icTheorems
    library_modules = $icLibraryFiles.Count
    permitted_axioms = @('propext','Classical.choice','Quot.sound')
    forbidden_construct_scan = 'passed'
    whitespace_scan = 'passed'
    module_coverage = 'passed'
    R0_snapshot_hashes = 'unchanged'
    source_hashes = @($icFiles | Sort-Object | ForEach-Object {
      @{path=$_; sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}
    })
  }
  $icReport | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification/manifest.json' -Encoding utf8
  Write-Output "Verified $icDeclarations declarations, $icTheorems theorem constants."
} finally {
  Set-Location -LiteralPath $icOriginalLocation
}


