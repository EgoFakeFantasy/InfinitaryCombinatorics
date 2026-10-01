$ErrorActionPreference = 'Stop'
$fmOriginalLocation = Get-Location
try {
  Set-Location -LiteralPath $PSScriptRoot
  New-Item -ItemType Directory -Path 'verification' -Force | Out-Null
  & (Join-Path $PSScriptRoot 'prepare-dependencies.ps1')
  $fmFiles = @('FIMADModels.lean', 'FIMADModels/CheckedBooleanZFC.lean', 'FIMADModels/UltrafilterTruth.lean',
    'FIMADModels/BooleanQuotient.lean', 'FIMADModels/PosetCompletion.lean',
    'FIMADModels/NaturalNames.lean', 'FIMADModels/UnboundedNames.lean',
    'FIMADModels/SplittingNames.lean', 'Audit.lean',
    'FIMADModels/UnboundedTruth.lean', 'FIMADModels/OmegaMinimal.lean',
    'FIMADModels/QuotientSplitting.lean',
    'FIMADModels/NativeZF.lean', 'FIMADModels/NativeFinite.lean',
    'FIMADModels/FiniteUnbounded.lean', 'FIMADModels/InfiniteSplitting.lean',
    'FIMADModels/ObjectTheory.lean', 'FIMADModels/ForcingFinite.lean', 'FIMADModels/Iteration.lean',
    'FIMADModels/IterationSchema.lean',
    'FIMADModels/DowInternal.lean', 'FIMADModels/FiniteStems.lean', 'FIMADModels/DowPoset.lean',
    'prepare-dependencies.ps1', 'dependency-patches/manifest.json',
    'dependency-patches/kernel-checked-axioms.patch',
    '.lake/packages/YesMetaZFC/YesMetaZFC/SetTheory/Axioms/Common.lean',
    '../Formalizations/FIMAD/PosetRegular.lean',
    '../Formalizations/FIMAD/BooleanEnumeration.lean',
    '../Formalizations/FIMAD/UnboundedSyntax.lean',
    '../Formalizations/FIMAD/InternalSemantics.lean',
    '../Formalizations/FIMAD/SetTheorySentence.lean', '../Formalizations/FIMAD/CheckedZFC.lean',
    'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'verify.ps1')
  $fmInitialHashes = @{}
  foreach ($fmFile in $fmFiles) {
    $fmInitialHashes[$fmFile] = (Get-FileHash -LiteralPath $fmFile -Algorithm SHA256).Hash
    if ($fmFile.EndsWith('.lean')) {
      $fmText = Get-Content -LiteralPath $fmFile -Raw -Encoding utf8
      if ($fmText -match '\b(sorry|admit|sorryAx|native_decide|unsafe)\b|(?m)^\s*(axiom|constant)\s') {
        throw "Forbidden construct in $fmFile"
      }
      if ($fmText -match '(?m)[ \t]+$|^(<<<<<<<|=======|>>>>>>>)') {
        throw "Whitespace or merge marker in $fmFile"
      }
    }
  }
  & lake build 2>&1 | Tee-Object -FilePath 'verification/build.log'
  if ($LASTEXITCODE -ne 0) { throw 'Typed model build failed' }
  & lake env lean Audit.lean 2>&1 | Tee-Object -FilePath 'verification/axiom-audit.log'
  if ($LASTEXITCODE -ne 0) { throw 'Typed model axiom audit failed' }
  $fmAudit = Get-Content -LiteralPath 'verification/axiom-audit.log' -Raw
  if ($fmAudit -notmatch 'Typed model audit passed: (\d+) declarations, (\d+) theorem constants') {
    throw 'Missing audit summary'
  }
  $fmDeclarations = [int]$Matches[1]
  $fmTheorems = [int]$Matches[2]
  foreach ($fmFile in $fmFiles) {
    if ((Get-FileHash -LiteralPath $fmFile -Algorithm SHA256).Hash -ne $fmInitialHashes[$fmFile]) {
      throw "Source changed during verification: $fmFile"
    }
  }
  $fmDependencies = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
  $fmReport = [ordered]@{
    checked_at_utc = [DateTime]::UtcNow.ToString('o')
    lean_toolchain = (Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim()
    yesmetazfc_revision = ($fmDependencies.packages | Where-Object name -eq 'YesMetaZFC').rev
    yesmetazfc_certificate_patch = 'dependency-patches/manifest.json'
    build = 'passed'
    axiom_audit = 'passed'
    declarations = $fmDeclarations
    theorem_constants = $fmTheorems
    permitted_axioms = @('propext', 'Classical.choice', 'Quot.sound')
    generic_boolean_zfc_model = 'proved'
    ordinary_quotient_truth_lemma = 'proved for all formulas and environments'
    ordinary_model_from_nonzero_value = 'constructed using Tarski ultrafilter extension and maximum principle'
    object_ZF_finite_unbounded_equivalences = 'proved in original Project.Derives'
    object_ZF_forcing_finite_bridge = 'proved in original Project.Derives'
    object_ZFC_finite_support_CCC = 'proved in original Project.Derives'
    object_ZFC_iteration_existence_schema = 'proved for every original successor BinarySchema with object specifications'
    object_ZF_Dow_same_stem_merge = 'proved for exact internal forbidden-stem conditions'
    object_ZFC_countable_finite_stems = 'proved with internal finite-set enumeration and injection'
    object_ZFC_Dow_poset_CCC = 'exact carrier, strengthening relation, maximum condition and CCC constructed'
    BMZ_specific_rule_and_preservation = 'not proved'
    specific_FIMAD_model_truth = 'not proved'
    formal_independence_complete = $false
    source_hashes = @($fmFiles | Sort-Object | ForEach-Object {
      @{path=$_; sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}
    })
  }
  $fmReport | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification/manifest.json' -Encoding utf8
  Write-Output "Verified typed model integration: $fmDeclarations declarations, $fmTheorems theorem constants."
} finally {
  Set-Location -LiteralPath $fmOriginalLocation
}
