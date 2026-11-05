#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/catalog.py check
lake build Colib
lake test
lake lint
lake exe mathlib/lint-style Colib ColibTest.Pilot ColibTest.References ColibTest.FiniteAlgebraImport \
  ColibTest.MilnorSymbols ColibTest.ExactGrothendieckGroup ColibTest.KoszulExt \
  ColibTest.MilnorProduct ColibTest.ExactFunctor ColibTest.SerreSubgroup ColibTest.SerreLocalization \
  ColibTest.MilnorExt ColibTest.KoszulCoefficients ColibTest.ExactPullbacks ColibTest.QConstruction \
  ColibTest.QFunctor ColibTest.QConnected ColibTest.PrincipalExt ColibTest.MilnorDescent \
  ColibTest.QuillenHomotopy ColibTest.QCore ColibTest.QuillenMap \
  ColibTest.NormalizedQ ColibTest.NerveHomotopy ColibTest.FiniteSimplexAdapter \
  ColibTest.CylinderPrerequisites ColibTest.PrismCoordinates ColibTest.PrismGluing \
  ColibTest.RealizationBridge ColibTest.QuillenFunctoriality ColibTest.QObjectClass \
  ColibTest.QGroupoid ColibTest.ObjectLoopsRegression \
  ColibTest.OpenCover ColibTest.SequentialCompactRegression \
  ColibTest.ConstantRealization ColibTest.CompletionNaturality ColibTest.PushoutOpenCover \
  ColibTest.SimplexBoundaryCollarRegression ColibTest.SimplexChartsAnnulusRegression \
  ColibTest.SimplexAttachment ColibTest.SimplexAttachmentGeneration \
  ColibTest.GraphAttachmentAnchors ColibTest.ExtQuotient ColibTest.MappingConeSign ColibTest.MilnorBaseFieldProduct ColibTest.MilnorNaturality ColibTest.MilnorPrincipalUnits ColibTest.MilnorRepeatedUniformizer ColibTest.MilnorResidueSurjectivity ColibTest.MilnorRightBaseFieldProduct ColibTest.MilnorRightUnitProduct ColibTest.MilnorSpecialization ColibTest.MilnorSpecializationProduct ColibTest.MilnorTransport ColibTest.MilnorUnitProduct ColibTest.MilnorUnramifiedMap ColibTest.MilnorUnramifiedMapAcross ColibTest.PrincipalExtOne ColibTest.PrincipalExtOneQuotient ColibTest.PrincipalGeneratorChange ColibTest.PrincipalGeneratorTransport ColibTest.PrincipalSeqGenerator ColibTest.PrincipalSeqGeneratorChange ColibTest.ProjectiveConnecting ColibTest.SingleConeLift ColibTest.TopExtClass ColibTest.TopExtGeneratorChange ColibTest.TopExtRingQuotient ColibTest.TopExtCoefficients ColibTest.ModuleQuasiIsoCriterion ColibTest.MilnorCoefficientRetraction ColibTest.KoszulCoefficientRegularity ColibTest.TopExtAllLengths ColibTest.TopExtAllNaturality ColibTest.MilnorResidueDegreeOne ColibTest.MilnorRamifiedDegreeOne ColibTest.KoszulCoefficientFunctor
lake exe mathlib/mk_all --lib Colib --check

# Aglib's pinned production auditor. This tool is separate from mathematical dependencies.
tool_root="${COLIB_TOOLS_DIR:-.lake/tools}"
auditor="$tool_root/axiom-audit"
if ! test -d "$auditor/.git"; then
  mkdir -p "$tool_root"
  git clone --depth 1 --branch v0.1.2 https://github.com/leanprover-community/axiom-audit.git "$auditor"
fi
test "$(git -C "$auditor" rev-parse HEAD)" = 46024e005996495c65ef609368e11ab39c4222e3
cp lean-toolchain "$auditor/lean-toolchain"
(cd "$auditor" && lake build)
lake env "$auditor/.lake/build/bin/axiom-audit" --root Colib

python3 scripts/catalog.py build
python3 scripts/site.py
