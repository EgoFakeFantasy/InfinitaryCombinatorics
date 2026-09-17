param([string]$OutputPath = (Join-Path (Split-Path $PSScriptRoot -Parent) 'infinitary-combinatorics-v0.1.0.zip'))
$ErrorActionPreference = 'Stop'
$icReport = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'verification/manifest.json') -Raw | ConvertFrom-Json
foreach ($icGate in @('build','consumer_examples','unfolded_R0_statements','formalization_statements','axiom_audit','module_coverage','forbidden_construct_scan')) {
  if ($icReport.$icGate -ne 'passed') { throw "Missing verification: $icGate" }
}
$icChecked = [Collections.Generic.HashSet[string]]::new()
foreach ($icSource in $icReport.source_hashes) {
  [void]$icChecked.Add($icSource.path)
  $icHash = (Get-FileHash -LiteralPath (Join-Path $PSScriptRoot $icSource.path) -Algorithm SHA256).Hash.ToLowerInvariant()
  if ($icHash -ne $icSource.sha256) { throw "Source changed since verification: $($icSource.path)" }
}
foreach ($icSource in (Get-ChildItem -LiteralPath (Join-Path $PSScriptRoot 'InfinitaryCombinatorics'),(Join-Path $PSScriptRoot 'R0'),(Join-Path $PSScriptRoot 'Formalizations') -Filter '*.lean' -Recurse)) {
  $icRelative = $icSource.FullName.Substring($PSScriptRoot.Length + 1).Replace('\','/')
  if (-not $icChecked.Contains($icRelative)) { throw "New unaudited module: $icRelative" }
}
$icPaths = @($icReport.source_hashes.path) + @(
  'README.md','AGENTS.md','.gitignore','lean-toolchain','lakefile.toml','lake-manifest.json',
  'verify.ps1','package.ps1','verification/manifest.json','verification/build.log',
  'verification/examples.log','verification/r0-statements.log','verification/axiom-audit.log',
  'verification/formalizations-statements.log',
  'docs/PROVENANCE.md','docs/ROADMAP.md','docs/SEMANTIC_REVIEW.md','docs/r0-source-hashes.json')
$icPaths += @(Get-ChildItem -LiteralPath (Join-Path $PSScriptRoot 'Formalizations') -Filter '*.md' -File -Recurse |
  ForEach-Object { $_.FullName.Substring($PSScriptRoot.Length + 1).Replace('\','/') })
$icPaths = @($icPaths | Sort-Object -Unique)
Add-Type -AssemblyName System.IO.Compression
Add-Type -AssemblyName System.IO.Compression.FileSystem
$icStream = [IO.File]::Open($OutputPath, [IO.FileMode]::Create)
$icZip = [IO.Compression.ZipArchive]::new($icStream, [IO.Compression.ZipArchiveMode]::Create)
try {
  foreach ($icRelative in $icPaths) {
    [IO.Compression.ZipFileExtensions]::CreateEntryFromFile($icZip,
      (Join-Path $PSScriptRoot $icRelative), 'infinitary-combinatorics/' + $icRelative) | Out-Null
  }
} finally {
  $icZip.Dispose()
  $icStream.Dispose()
}
$icReadback = [IO.Compression.ZipFile]::OpenRead($OutputPath)
try {
  if ($icReadback.Entries.Count -ne $icPaths.Count) { throw 'Archive entry count mismatch' }
  foreach ($icRelative in $icPaths) {
    $icEntry = $icReadback.GetEntry('infinitary-combinatorics/' + $icRelative)
    if ($null -eq $icEntry) { throw "Missing archive entry: $icRelative" }
    $icEntryStream = $icEntry.Open()
    $icHasher = [Security.Cryptography.SHA256]::Create()
    try {
      $icArchivedHash = [BitConverter]::ToString($icHasher.ComputeHash($icEntryStream)).Replace('-','')
      $icSourceHash = (Get-FileHash -LiteralPath (Join-Path $PSScriptRoot $icRelative) -Algorithm SHA256).Hash
      if ($icArchivedHash -ne $icSourceHash) { throw "Archive hash mismatch: $icRelative" }
    } finally { $icEntryStream.Dispose(); $icHasher.Dispose() }
  }
} finally { $icReadback.Dispose() }
$icArchiveHash = (Get-FileHash -LiteralPath $OutputPath -Algorithm SHA256).Hash.ToLowerInvariant()
"$icArchiveHash  $([IO.Path]::GetFileName($OutputPath))" | Set-Content -LiteralPath ($OutputPath + '.sha256') -Encoding utf8
Write-Output "Packaged and checked $($icPaths.Count) files: $OutputPath"
