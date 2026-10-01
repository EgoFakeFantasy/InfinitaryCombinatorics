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
    'FIMADModels/DowDense.lean', 'FIMADModels/DowAvoid.lean', 'FIMADModels/DowSeparator.lean',
    'FIMADModels/DowGeneric.lean', 'FIMADModels/DowExtension.lean',
    'FIMADModels/DowAmalgamation.lean', 'FIMADModels/DowReach.lean',
    'FIMADModels/DowPossible.lean', 'FIMADModels/DowFiniteTail.lean',
    'FIMADModels/DowTests.lean', 'FIMADModels/DowTestAssembly.lean', 'FIMADModels/DowTestExistence.lean',
    'FIMADModels/DowValueTails.lean', 'FIMADModels/DowTallTests.lean', 'FIMADModels/DowTallness.lean',
    'FIMADModels/CheckDecisions.lean', 'FIMADModels/DowNameTests.lean', 'FIMADModels/DowNameTheorem.lean',
    'FIMADModels/DowNameExtension.lean', 'FIMADModels/DowNameFamily.lean',
    'FIMADModels/DowNameFamilyTheorem.lean', 'FIMADModels/DowNameSplitting.lean',
    'FIMADModels/DowSplittingSyntax.lean', 'FIMADModels/DowSplittingForcing.lean',
    'FIMADModels/DowOmegaSplitting.lean',
    'FIMADModels/DowInfiniteNames.lean',
    'FIMADModels/NameNormalization.lean', 'FIMADModels/NameNormalizationFamily.lean',
    'FIMADModels/DowConditionalPreservation.lean', 'FIMADModels/DowConditionalTheorem.lean',
    'FIMADModels/CountableRealEnumeration.lean', 'FIMADModels/FunctionValueNames.lean',
    'FIMADModels/FunctionCanonicalValues.lean', 'FIMADModels/ExtensionFamilyNames.lean',
    'FIMADModels/DowExtensionPreservation.lean', 'FIMADModels/DowPreservationTheorem.lean',
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
  # Every local typed module must be hash-checked and reachable from the audited umbrella.
  $fmModules = @{'FIMADModels' = 'FIMADModels.lean'}
  foreach ($fmSource in Get-ChildItem -LiteralPath 'FIMADModels' -Filter '*.lean' -Recurse) {
    $fmRelative = $fmSource.FullName.Substring($PSScriptRoot.Length + 1).Replace('\','/')
    if ($fmRelative -notin $fmFiles) { throw "Unhashed typed module: $fmRelative" }
    $fmModules[$fmRelative.Replace('/','.').Replace('.lean','')] = $fmRelative
  }
  $fmQueue = [Collections.Generic.Queue[string]]::new()
  $fmSeen = [Collections.Generic.HashSet[string]]::new()
  $fmQueue.Enqueue('FIMADModels')
  while ($fmQueue.Count -gt 0) {
    $fmModule = $fmQueue.Dequeue()
    if (-not $fmSeen.Add($fmModule)) { continue }
    $fmText = Get-Content -LiteralPath $fmModules[$fmModule] -Raw
    foreach ($fmMatch in [regex]::Matches($fmText, '(?m)^import\s+([A-Za-z0-9_.]+)\s*$')) {
      $fmImport = $fmMatch.Groups[1].Value
      if ($fmModules.ContainsKey($fmImport)) { $fmQueue.Enqueue($fmImport) }
    }
  }
  foreach ($fmModule in $fmModules.Keys) {
    if (-not $fmSeen.Contains($fmModule)) { throw "Unaudited typed module: $fmModule" }
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
    module_coverage = 'passed'
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
    object_ZF_Dow_dense_requirements = 'both hitting and finite-avoidance extensions proved in original Project.Derives'
    object_ZF_Dow_directed_separator = 'proved with explicit directed-set and meeting hypotheses'
    native_ZFC_Dow_generic_extension = 'actual internal union-of-stems name, exact quotient value and weak separator for enumerated ground models'
    object_ZF_Dow_finite_amalgamation = 'internally finite same-stem families merged by original finite-set induction'
    object_ZF_Dow_dense_stem_closure = 'actual least closed set constructed and all finite stems reached'
    object_ZFC_Dow_finite_possible_values = 'internal finite elimination and finite-tail argument proved'
    object_ZFC_Dow_countable_possible_value_tests = 'actual internal countable tests constructed for each finite stem from a monotone dense natural-value decision relation'
    object_ZFC_Dow_tallness_tests = 'one internal countable family controls every stem and natural bound for monotone unbounded decision relations'
    object_ZFC_Dow_actual_name_tests = 'actual membership decision graphs derived from the translated unbounded-name formula'
    object_ZFC_Dow_countable_name_tests = 'one internal countable test family for every internally countable family of globally forced unbounded names'
    object_ZF_Dow_forced_splitting = 'original splitting formula forced from actual test-family splitting; proved through all generic quotients and public reflection criterion'
    object_ZFC_Dow_countable_name_preservation = 'an internal omega-splitting family supplies one ground splitter whose canonical name is forced to split every input real name'
    original_infinite_name_input_bridge = 'native and forced original infinitude imply the exact unbounded-name formula; original ZF derivation and actual countable-name application proved'
    object_ZFC_infinite_name_normalization = 'actual global infinite real name, forced equal to the original wherever that original is forced an infinite real; original ZFC derivation'
    object_ZFC_conditional_countable_name_preservation = 'arbitrary internally countable ground name sets, with original infinitude required only at the conclusion condition'
    object_ZF_countable_real_enumeration = 'internal omega-function covering every countable family of infinite reals, including empty and finite cases'
    arbitrary_extension_countable_infinite_real_family_coding = 'proved using quotient-internal enumeration, original maximum principle, collection and canonical indices'
    object_ZFC_Dow_full_single_step_omega_splitting_preservation = 'original ZFC derivation of genuine forcing assertion, covering every countable extension family; no abstract preservation certificate'
    arbitrary_extension_countable_family_coding_and_localization = 'proved for the infinite-real families needed by omega-splitting'
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
