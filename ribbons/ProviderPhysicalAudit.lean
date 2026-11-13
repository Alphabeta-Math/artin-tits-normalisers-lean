import Lean.Elab.Command
import Lean.Util.CollectAxioms
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver
import OAI.Topology.ArtinGroups.Quivers.VertexHom
import OAI.Topology.ArtinGroups.Harmonic.GeneratorPlacement
import OAI.Topology.ArtinGroups.Harmonic.Level
import OAI.Topology.ArtinGroups.Quivers.SmulMul
import OAI.Topology.ArtinGroups.Quivers.Path
import OAI.Topology.ArtinGroups.Quivers.CornerPath
import OAI.Topology.ArtinGroups.Quivers.SimpleEdge
import OAI.Topology.ArtinGroups.Quivers.ExtArrow
import OAI.Topology.ArtinGroups.Model
import OAI.Topology.ArtinGroups.DeligneDefinitions
import OAI.Topology.ArtinGroups.Harmonic.CosetVertex
import OAI.Topology.ArtinGroups.Coxeter.Signs
import OAI.Topology.ArtinGroups.Coxeter.Parabolic
import OAI.Topology.ArtinGroups.Coxeter.AltList
import OAI.Topology.ArtinGroups.Geometry.Reflect
import OAI.Topology.ArtinGroups.Geometry.TrigPhasePower
import OAI.Topology.ArtinGroups.Geometry.Cartan
import OAI.Topology.ArtinGroups.Geometry.TrigPhaseSqPrimitive
import OAI.Topology.ArtinGroups.Coxeter.AltListPairDescent
import OAI.Topology.ArtinGroups.Coxeter.ReducedWordProperty
import OAI.Topology.ArtinGroups.Harmonic.ReducedExpression
import OAI.Topology.ArtinGroups.Coxeter.InverseParabolicMinimum
import OAI.Topology.ArtinGroups.Realizations.CellDeligne
import OAI.Topology.ArtinGroups.Coxeter.RightParabolicDecomposition
import OAI.Topology.ArtinGroups.Geometry.DihedralScalar
import OAI.Topology.ArtinGroups.Coxeter.AltNext
import OAI.Topology.ArtinGroups.Coxeter.AlternatingNextRoot
import OAI.Topology.ArtinGroups.Geometry.RootCoeffAltExtension
import OAI.Topology.ArtinGroups.Geometry.RootNonnegAscent
import OAI.Topology.ArtinGroups.Geometry.RootNonposDescent
import OAI.Topology.ArtinGroups.Geometry.LongestMulSelf
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRelations
import OAI.Topology.ArtinGroups.Harmonic.PositiveDegreeHom
import OAI.Topology.ArtinGroups.Harmonic.PositiveSimpleLiftMul
import OAI.Topology.ArtinGroups.Coxeter.WeakPrefix
import OAI.Topology.ArtinGroups.Coxeter.CommonWeakPrefixMaximal
import OAI.Topology.ArtinGroups.Harmonic.PositivePrefix
import OAI.Topology.ArtinGroups.Harmonic.SimpleFrontLink
import OAI.Topology.ArtinGroups.Harmonic.WordFrontData
import OAI.Topology.ArtinGroups.Harmonic.PositiveHead
import OAI.Topology.ArtinGroups.Harmonic.PositivePrefixMulLeft
import OAI.Topology.ArtinGroups.Harmonic.PositiveReverseHom
import OAI.Topology.ArtinGroups.Harmonic.PositiveLiftSimple
import OAI.Topology.ArtinGroups.Harmonic.FiniteArtinPositiveLeft
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Quivers.CornerScalar
import OAI.Topology.ArtinGroups.Cancellation.CornerRemainder
import OAI.Topology.ArtinGroups.Cancellation.ScalarPivot
import OAI.Topology.ArtinGroups.Cancellation.Retained
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Quivers.TestIndex
import OAI.Topology.ArtinGroups.Quivers.TestPlacement
import OAI.Topology.ArtinGroups.Quivers.Dual
import OAI.Topology.ArtinGroups.Quivers.CotestPlacement
import OAI.Topology.ArtinGroups.Complexes.ConePlacement
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement
import OAI.Topology.ArtinGroups.Quivers.TestTransform
import OAI.Topology.ArtinGroups.Complexes.ConeMap
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistHomotopy
import OAI.Topology.ArtinGroups.Quivers.SelfCornerEquiv
import OAI.Topology.ArtinGroups.Complexes.Reindex
import OAI.Topology.ArtinGroups.Complexes.InverseTwistIndex
import OAI.Topology.ArtinGroups.Complexes.InverseTwistDifferential
import OAI.Topology.ArtinGroups.Complexes.InverseTwistPlacement
import OAI.Topology.ArtinGroups.Diagrams.Index
import OAI.Topology.ArtinGroups.Complexes.InverseTwistIdentity
import OAI.Topology.ArtinGroups.Complexes.NormalizedInverseTwistHomotopy
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistIndexEquiv
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistDifferential
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistProjection
import OAI.Topology.ArtinGroups.Diagrams.ReverseDifferential
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistProjectionCommute
import OAI.Topology.ArtinGroups.Complexes.NormalizedReverseTwistHomotopy
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Complexes.CommuteTwistSwap
import OAI.Topology.ArtinGroups.Cancellation.BlockPivot
import OAI.Topology.ArtinGroups.Cancellation.ReducedDifferential
import OAI.Topology.ArtinGroups.Cancellation.ReducedDifferential2
import OAI.Topology.ArtinGroups.Coxeter.BraidCoreIndex
import OAI.Topology.ArtinGroups.Coxeter.BraidFirstPivot
import OAI.Topology.ArtinGroups.Quivers.EdgeContraction
import OAI.Topology.ArtinGroups.Coxeter.BraidCoreFirstTarget
import OAI.Topology.ArtinGroups.Coxeter.BraidSecondPivot
import OAI.Topology.ArtinGroups.Coxeter.BraidCorePlacement
import OAI.Topology.ArtinGroups.Complexes.FiniteHomotopySetoid
import OAI.Topology.ArtinGroups.Complexes.UnfoldedPresentation
import OAI.Topology.ArtinGroups.Harmonic.QuantumNumber
import OAI.Topology.ArtinGroups.Harmonic.FusionLabel
import OAI.Topology.ArtinGroups.Harmonic.FusionVertex
import OAI.Topology.ArtinGroups.Harmonic.FusionQuiverSimpleEdge
import OAI.Topology.ArtinGroups.Quivers.Level
import OAI.Topology.ArtinGroups.Complexes.HomSpace
import OAI.Topology.ArtinGroups.Complexes.HomPath
import OAI.Topology.ArtinGroups.Complexes.PositiveHomTransform
import OAI.Topology.ArtinGroups.Quivers.TraceLinear
import OAI.Topology.ArtinGroups.Complexes.HomOperator
import OAI.Topology.ArtinGroups.Complexes.ReindexHomOperator
import OAI.Topology.ArtinGroups.Complexes.HomSpaceMul
import OAI.Topology.ArtinGroups.Complexes.CorrectionBoundary
import OAI.Topology.ArtinGroups.Complexes.InverseHomMatrix
import OAI.Topology.ArtinGroups.Complexes.NegativeHomTransformReflect
import OAI.Topology.ArtinGroups.Complexes.HomDimension
import OAI.Topology.ArtinGroups.Harmonic.InjectiveFinrankOne
import OAI.Topology.ArtinGroups.Complexes.HomDetector
import OAI.Topology.ArtinGroups.Complexes.DiagonalVertex
import OAI.Topology.ArtinGroups.Quivers.LinearMatrix
import OAI.Topology.ArtinGroups.Complexes.HomSpacePairing
import OAI.Topology.ArtinGroups.Complexes.HomSpaceDuality
import OAI.Topology.ArtinGroups.Complexes.HomStep
import OAI.Topology.ArtinGroups.Complexes.HomInternalSupport
import OAI.Topology.ArtinGroups.Complexes.CornerPath
import OAI.Topology.ArtinGroups.Complexes.ExtendLayer
import OAI.Topology.ArtinGroups.Complexes.DifferentialMulExtendLayer
import OAI.Topology.ArtinGroups.Quivers.PathZero
import OAI.Topology.ArtinGroups.Complexes.RestrictLayer
import OAI.Topology.ArtinGroups.Quivers.CoefficientMatrix
import OAI.Topology.ArtinGroups.Quivers.PathTwo
import OAI.Topology.ArtinGroups.Quivers.PathTwoSelf
import OAI.Topology.ArtinGroups.Complexes.Capped
import OAI.Topology.ArtinGroups.Complexes.MatrixOneMulExtend
import OAI.Topology.ArtinGroups.Quivers.VertexLinear
import OAI.Topology.ArtinGroups.Complexes.SecondaryLayer
import OAI.Topology.ArtinGroups.Complexes.RestrictExtendLayerMul
import OAI.Topology.ArtinGroups.Complexes.PureHomSpaceHomogeneous
import OAI.Topology.ArtinGroups.Complexes.LeftMatrix
import OAI.Topology.ArtinGroups.Complexes.SummandSecondary
import OAI.Topology.ArtinGroups.Complexes.PureCoefficientCohomology
import OAI.Topology.ArtinGroups.Complexes.CoefficientSocle
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDual
import OAI.Topology.ArtinGroups.Diagrams.SupportedKernel
import OAI.Topology.ArtinGroups.Quivers.UnitTestVector
import OAI.Topology.ArtinGroups.Complexes.CoefficientSocleRestrictLayer
import OAI.Topology.ArtinGroups.Complexes.TestComplexVertexDifferential
import OAI.Topology.ArtinGroups.Complexes.TwistNewTestIndex
import OAI.Topology.ArtinGroups.Complexes.ScalarSupported
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistOtherTest2
import OAI.Topology.ArtinGroups.Complexes.TokenShift
import OAI.Topology.ArtinGroups.Complexes.ScalarSupportedTokenShift
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistOtherTest3
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector
import OAI.Topology.ArtinGroups.Complexes.GeneratorTokenTest
import OAI.Topology.ArtinGroups.Complexes.Test
import OAI.Topology.ArtinGroups.Complexes.TestUpperBound
import OAI.Topology.ArtinGroups.Complexes.ArrowShift
import OAI.Topology.ArtinGroups.Complexes.ScalarSupportedCochainShift
import OAI.Topology.ArtinGroups.Complexes.TestExact
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRel
import OAI.Topology.ArtinGroups.Coxeter.OrdinaryCoxeterMatrix
import OAI.Topology.ArtinGroups.Harmonic.HarmonicExtension
import OAI.Topology.ArtinGroups.Harmonic.FusionFold
import OAI.Topology.ArtinGroups.Harmonic.FiniteFusionEdge
import OAI.Topology.ArtinGroups.Geometry.InvariantForm
import OAI.Topology.ArtinGroups.Geometry.StrictChamber
import OAI.Topology.ArtinGroups.Geometry.CartanOffNonpos
import OAI.Topology.ArtinGroups.Geometry.Form
import OAI.Topology.ArtinGroups.Geometry.SphericalCartanPos
import OAI.Topology.ArtinGroups.Harmonic.SphericalFoldedMatrix
import OAI.Topology.ArtinGroups.Harmonic.RowReflect
import OAI.Topology.ArtinGroups.Geometry.CoordinateExtension
import OAI.Topology.ArtinGroups.Coxeter.RestrictedMatrix
import OAI.Topology.ArtinGroups.Geometry.CartanRestricted
import OAI.Topology.ArtinGroups.Geometry.RestrictionLength
import OAI.Topology.ArtinGroups.Geometry.RootPair
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedMatrix
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedHom
import OAI.Topology.ArtinGroups.Geometry.RootRowOrthogonalWord
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedColorOrthogonal
import OAI.Topology.ArtinGroups.Coxeter.WordProdEquiv
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusion
import OAI.Topology.ArtinGroups.Coxeter.AltListReduced
import OAI.Topology.ArtinGroups.Harmonic.SphericalPair
import OAI.Topology.ArtinGroups.Coxeter.AltListMap
import OAI.Topology.ArtinGroups.Quivers.Iso
import OAI.Topology.ArtinGroups.Quivers.PacketIndex
import OAI.Topology.ArtinGroups.Complexes.PacketConsEquiv
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex
import OAI.Topology.ArtinGroups.Complexes.FiniteSum
import OAI.Topology.ArtinGroups.Complexes.FiniteSum2
import OAI.Topology.ArtinGroups.Complexes.Sum
import OAI.Topology.ArtinGroups.Complexes.PacketPermReindex
import OAI.Topology.ArtinGroups.Functors.Path
import OAI.Topology.ArtinGroups.Functors.Placement
import OAI.Topology.ArtinGroups.Functors.TestIndex
import OAI.Topology.ArtinGroups.Functors.ReversibleQuiverMap
import OAI.Topology.ArtinGroups.Complexes.HomDimension2
import OAI.Topology.ArtinGroups.Complexes.InitialProjective
import OAI.Topology.ArtinGroups.Complexes.HomDimensionZeroHom
import OAI.Topology.ArtinGroups.Complexes.Initial
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Complexes.Refl
import OAI.Topology.ArtinGroups.Diagrams.TransposeConjugateEquiv
import OAI.Topology.ArtinGroups.Complexes.PureSupportedCycles
import OAI.Topology.ArtinGroups.Complexes.MinimalModelEquivalence
import OAI.Topology.ArtinGroups.Harmonic.Crossing
import OAI.Topology.ArtinGroups.Quivers.VertexIdMulPath
import OAI.Topology.ArtinGroups.Quivers.StringArrow
import OAI.Topology.ArtinGroups.Functors.PathImage
import OAI.Topology.ArtinGroups.Functors.Index
import OAI.Topology.ArtinGroups.Harmonic.LeftSector
import OAI.Topology.ArtinGroups.Functors.PathMarked
import OAI.Topology.ArtinGroups.Functors.BasePath
import OAI.Topology.ArtinGroups.Functors.PathSwitchEquiv
import OAI.Topology.ArtinGroups.Functors.Evaluation
import OAI.Topology.ArtinGroups.Functors.SectorInverse
import OAI.Topology.ArtinGroups.Functors.CoordinateExpansion
import OAI.Topology.ArtinGroups.Realizations.MulBlockDiagonal'Entry
import OAI.Topology.ArtinGroups.Functors.LeftHomIndex
import OAI.Topology.ArtinGroups.Quivers.ScalarCornerMatrixDegree
import OAI.Topology.ArtinGroups.Functors.LeftHomPlacement
import OAI.Topology.ArtinGroups.Functors.HomSupportedCyclesEquiv
import OAI.Topology.ArtinGroups.Functors.LeftSocleIndexEquiv
import OAI.Topology.ArtinGroups.Functors.HomDualSupportedCycles
import OAI.Topology.ArtinGroups.Functors.HomSwitchMap
import OAI.Topology.ArtinGroups.Functors.LeftPacketIndex
import OAI.Topology.ArtinGroups.Functors.PacketSwitchMatrix
import OAI.Topology.ArtinGroups.Functors.ConeIndexEquiv
import OAI.Topology.ArtinGroups.Complexes.ReindexConeIsomorphism
import OAI.Topology.ArtinGroups.Functors.PacketTwistComparison
import OAI.Topology.ArtinGroups.Functors.ColorPacketPerm
import OAI.Topology.ArtinGroups.Functors.LayerIndexEquiv
import OAI.Topology.ArtinGroups.Complexes.SumTestEquiv
import OAI.Topology.ArtinGroups.Complexes.LayerSocleDimensionSum
import OAI.Topology.ArtinGroups.Functors.SeedEquiv
import OAI.Topology.ArtinGroups.Functors.SignedPacketPerm
import OAI.Topology.ArtinGroups.Harmonic.EigenvectorProportional
import OAI.Topology.ArtinGroups.Harmonic.SumNeighborsSubtype
import OAI.Topology.ArtinGroups.Functors.WordOrbitSocleAdjacency
import OAI.Topology.ArtinGroups.Quivers.VertexMinimal
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistFiberEquiv
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray2
import OAI.Topology.ArtinGroups.Complexes.LevelArrayComplexMinimal
import OAI.Topology.ArtinGroups.Functors.LevelGeneratorEquiv
import OAI.Topology.ArtinGroups.Functors.WordOrbitCountAdjacency
import OAI.Topology.ArtinGroups.Harmonic.StringAdjacent
import OAI.Topology.ArtinGroups.Harmonic.FusionRest
import OAI.Topology.ArtinGroups.Harmonic.FusionFactorStep
import OAI.Topology.ArtinGroups.Complexes.OptionSumEquiv
import OAI.Topology.ArtinGroups.Functors.WordPacketPermAppend
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketPerm
import OAI.Topology.ArtinGroups.Coxeter.AlternatingLiftProd
import OAI.Topology.ArtinGroups.Quivers.OffDiagonalVertexZero
import OAI.Topology.ArtinGroups.Quivers.ProbeVertex
import OAI.Topology.ArtinGroups.Quivers.ProbeSimpleEdge
import OAI.Topology.ArtinGroups.Harmonic.ProbePacket
import OAI.Topology.ArtinGroups.Complexes.MinimalEmbedding
import OAI.Topology.ArtinGroups.Complexes.ActedIndex
import OAI.Topology.ArtinGroups.Quivers.LengthCases
import OAI.Topology.ArtinGroups.Complexes.ReducedAmplitudeTwistLevel
import OAI.Topology.ArtinGroups.Complexes.MinimalGeneratorDualCycle
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDualRestrict
import OAI.Topology.ArtinGroups.Complexes.PacketTwistRaisedGenerator
import OAI.Topology.ArtinGroups.Complexes.NegativeAmplitudeCoreIndex
import OAI.Topology.ArtinGroups.Complexes.ReducedNegativeAmplitudeTwist
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistLoweredGenerator
import OAI.Topology.ArtinGroups.Complexes.UpperBound
import OAI.Topology.ArtinGroups.Complexes.BottomScalarCycleZero
import OAI.Topology.ArtinGroups.Complexes.LayerVector
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistLowerBound
import OAI.Topology.ArtinGroups.Complexes.ComplexPacketLowerBound
import OAI.Topology.ArtinGroups.Coxeter.OrdinaryTwistBraid
import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionAppend
import OAI.Topology.ArtinGroups.Complexes.PacketPermEnumeration
import OAI.Topology.ArtinGroups.Harmonic.FusionExpandedWordAction
import OAI.Topology.ArtinGroups.Harmonic.FusionExpandedWordPerm
import OAI.Topology.ArtinGroups.Harmonic.SphericalPacketWordProperty
import OAI.Topology.ArtinGroups.Harmonic.ArtinAction
import OAI.Topology.ArtinGroups.Complexes.PositiveTopDivisor
import OAI.Topology.ArtinGroups.Complexes.ReducedNoTopDivisor
import OAI.Topology.ArtinGroups.Complexes.OutsideCap
import OAI.Topology.ArtinGroups.Complexes.PositiveWordLowerBound
import OAI.Topology.ArtinGroups.Complexes.PlacedProjective
import OAI.Topology.ArtinGroups.Complexes.InverseWordAction
import OAI.Topology.ArtinGroups.Quivers.ClosedNeighborhood
import OAI.Topology.ArtinGroups.Complexes.HighestLocalGeneratorTest
import OAI.Topology.ArtinGroups.Complexes.InverseWordActionAppend
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistCapDisjoint
import OAI.Topology.ArtinGroups.Harmonic.ArtinActionWordArtin
import OAI.Topology.ArtinGroups.Complexes.PureUpperBoundariesZero
import OAI.Topology.ArtinGroups.Complexes.PureTotalHomEuler
import OAI.Topology.ArtinGroups.Complexes.EqualColorPair
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector
import OAI.Topology.ArtinGroups.Complexes.BlockClosed
import OAI.Topology.ArtinGroups.Complexes.ColorBoundary
import OAI.Topology.ArtinGroups.Complexes.TermwiseSplitInjection
import OAI.Topology.ArtinGroups.Complexes.FrameModelLayerMiddle
import OAI.Topology.ArtinGroups.Complexes.HomDimensionZeroCycles
import OAI.Topology.ArtinGroups.Complexes.DownClosed
import OAI.Topology.ArtinGroups.Complexes.LowMatrix
import OAI.Topology.ArtinGroups.Complexes.LowerTruncation
import OAI.Topology.ArtinGroups.Complexes.TargetLow
import OAI.Topology.ArtinGroups.Complexes.HomMono
import OAI.Topology.ArtinGroups.Complexes.Shift
import OAI.Topology.ArtinGroups.Complexes.ScalarKernel
import OAI.Topology.ArtinGroups.Complexes.InverseMatrix
import OAI.Topology.ArtinGroups.Complexes.HomotopyConeMap
import OAI.Topology.ArtinGroups.Complexes.Cone
import OAI.Topology.ArtinGroups.Complexes.LayerConeEquivalence
import OAI.Topology.ArtinGroups.Quivers.SignDiagonal
import OAI.Topology.ArtinGroups.Complexes.NegativeConeIndex
import OAI.Topology.ArtinGroups.Complexes.HighConeIndex
import OAI.Topology.ArtinGroups.Complexes.EmptyTestIndex
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistModern
import OAI.Topology.ArtinGroups.Complexes.PureLayerSelf
import OAI.Topology.ArtinGroups.Complexes.LayerSocleDimensionLayer
import OAI.Topology.ArtinGroups.Harmonic.PositiveWord
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWord
import OAI.Topology.ArtinGroups.Harmonic.ProbeCoreInclusion
import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionOrthogonal
import OAI.Topology.ArtinGroups.Harmonic.RestrictedArtinHom
import OAI.Topology.ArtinGroups.Harmonic.MaximalReducedPositivePrefix
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordAppend
import OAI.Topology.ArtinGroups.Complexes.ScalarExactNotZero
import OAI.Topology.ArtinGroups.Complexes.InitialProbeTestUpper
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordInitial
import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionTest
import OAI.Topology.ArtinGroups.Harmonic.Extend
import OAI.Topology.ArtinGroups.Complexes.UnfoldedCartanSymm
import OAI.Topology.ArtinGroups.Complexes.InitialHomSpaceNegative
import OAI.Topology.ArtinGroups.Complexes.SupportedCoefficientCycles
import OAI.Topology.ArtinGroups.Functors.ComplexInitial
import OAI.Topology.ArtinGroups.Diagrams.CongrEquiv
import OAI.Topology.ArtinGroups.Functors.SupportedCycles
import OAI.Topology.ArtinGroups.Functors.ComplexPureLayer
import OAI.Topology.ArtinGroups.Realizations.FusionWeightSplit
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketOrbit
import OAI.Topology.ArtinGroups.Complexes.PacketPermAction
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketAction
import OAI.Topology.ArtinGroups.Complexes.LayerTotalHomDimension
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitModel
import OAI.Topology.ArtinGroups.Harmonic.FusionQuiverCartan
import OAI.Topology.ArtinGroups.Complexes.GeneratorVectorPureLayer
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitMultiplicity
import OAI.Topology.ArtinGroups.Functors.ComplexLowerTruncation
import OAI.Topology.ArtinGroups.Functors.TruncationIndexEquiv
import OAI.Topology.ArtinGroups.Complexes.SumTruncationEquiv
import OAI.Topology.ArtinGroups.Complexes.LowerTruncationSum
import OAI.Topology.ArtinGroups.Harmonic.LayerExpression
import OAI.Topology.ArtinGroups.Harmonic.FusionExpressionAction
import OAI.Topology.ArtinGroups.Harmonic.FusionExpressionOrbit
import OAI.Topology.ArtinGroups.Complexes.CanonicalWordLow
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionLow
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionLowCount
import OAI.Topology.ArtinGroups.Complexes.PlacementSignedWeight
import OAI.Topology.ArtinGroups.Complexes.CochainSignSubOne
import OAI.Topology.ArtinGroups.Complexes.TotalVector
import OAI.Topology.ArtinGroups.Complexes.TotalVectorLayer
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionMultiplicity
import OAI.Topology.ArtinGroups.Harmonic.FusionZeroLabel
import OAI.Topology.ArtinGroups.Harmonic.InitialProbe
import OAI.Topology.ArtinGroups.Harmonic.MaximalReducedMonoidPrefix
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordPositive
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordMonoid
import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelMonoid
import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelLeft
import OAI.Topology.ArtinGroups.Harmonic.PositiveDegreeSublevelFinite
import OAI.Topology.ArtinGroups.Harmonic.SphericalPositiveCommonMultiple
import OAI.Topology.ArtinGroups.Harmonic.RestrictionHomRange

/-!
# Physical provider declaration coverage

Read the same serialized parts as exact single-module kernel replay and compare
all physical constants to the canonical imported declarations whose transitive
axioms are checked here. Overlap is permitted only for structurally identical
theorems, with identical types, values and universe parameters. This harness
adds no mathematical assumptions and does not repeat kernel replay.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

/-- Same physical-part reader used by the reviewed project audit. -/
def providerPhysicalReadParts (module : Lean.Name) : IO (Array (Lean.ModuleData × Lean.CompactedRegion)) := do
  let file ← Lean.findOLean module
  unless (← file.pathExists) do
    throw <| IO.userError s!"Missing provider compiled module: {module}"
  let mut files := #[file]
  let server := Lean.OLeanLevel.server.adjustFileName file
  if (← server.pathExists) then
    files := files.push server
    let privatePart := Lean.OLeanLevel.private.adjustFileName file
    if (← privatePart.pathExists) then files := files.push privatePart
  Lean.readModuleDataParts files

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected := env.header.moduleNames.filter fun mod => mod.toString.startsWith "OAI."
  unless expected.size == 359 do
    throwError "Expected 359 imported provider modules, found {expected.size}"
  let mut canonicalNames : Std.HashMap Name Name := {}
  let mut canonicalCount : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx]!
      if expected.contains mod then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Forbidden canonical provider axiom {ax} in {name} ({mod})"
        canonicalNames := canonicalNames.insert name mod
        canonicalCount := canonicalCount + 1
  if canonicalCount == 0 then throwError "Empty canonical provider audit"
  let mut physicalNames : Std.HashMap Name Nat := {}
  let mut physicalCount : Nat := 0
  let mut duplicateCount : Nat := 0
  for mod in expected do
    let parts ← providerPhysicalReadParts mod
    if empty : parts.size = 0 then
      throwError "Empty physical provider module data: {mod}"
    else
      let last := parts[parts.size - 1]
      unless last.1.constNames.size == last.1.constants.size do
        throwError "Physical name/constant array length mismatch: {mod}"
      let mut names : Array String := #[]
      for name in last.1.constNames, ci in last.1.constants do
        unless name == ci.name do throwError "Compiled name/constant mismatch in {mod}"
        let some owner := canonicalNames.get? name |
          throwError "Physical declaration outside canonical provider axiom coverage: {name} ({mod})"
        let some imported := env.find? name |
          throwError "Physical declaration absent from imported audit environment: {name} ({mod})"
        unless ci.type == imported.type && ci.value? == imported.value? &&
            ci.levelParams == imported.levelParams do
          throwError "Physical/imported declaration content mismatch: {name} ({mod})"
        unless owner == mod do
          match ci, imported with
          | .thmInfo _, .thmInfo _ => pure ()
          | _, _ => throwError "Unexpected non-theorem declaration overlap: {name} ({mod}, {owner})"
          unless expected.contains owner do
            throwError "Overlapping provider declaration owned outside audited modules: {name} ({owner})"
          duplicateCount := duplicateCount + 1
          let row := Json.mkObj [
            ("name", toJson name.toString), ("physical_module", toJson mod.toString),
            ("canonical_module", toJson owner.toString), ("same_type", toJson true),
            ("same_proof", toJson true), ("same_universe_parameters", toJson true),
            ("theorem_in_both", toJson true)]
          logInfo m!"PROVIDER_PHYSICAL_DUPLICATE_JSON {row.compress}"
        names := names.push name.toString
        physicalNames := physicalNames.insert name (physicalNames.getD name 0 + 1)
        physicalCount := physicalCount + 1
      if names.isEmpty then
        throwError "Provider module has no physical declarations: {mod}"
      let row := Json.mkObj [
        ("module", toJson mod.toString), ("declarations", toJson names.size),
        ("names", toJson names.toList)]
      logInfo m!"PROVIDER_PHYSICAL_MODULE_JSON {row.compress}"
  for (name, _) in canonicalNames.toList do
    unless physicalNames.contains name do
      throwError "Canonical provider declaration has no physical occurrence: {name}"
  unless physicalNames.size == canonicalCount && physicalCount == canonicalCount + duplicateCount do
    throwError "Physical/canonical provider declaration coverage mismatch"
  let row := Json.mkObj [
    ("modules", toJson expected.size), ("canonical_declarations", toJson canonicalCount),
    ("physical_occurrences", toJson physicalCount),
    ("distinct_physical_names", toJson physicalNames.size),
    ("identical_theorem_duplicates", toJson duplicateCount),
    ("canonical_axioms_checked", toJson true),
    ("all_physical_type_value_universe_parameters_identical", toJson true)]
  logInfo m!"PROVIDER_PHYSICAL_SUMMARY_JSON {row.compress}"
