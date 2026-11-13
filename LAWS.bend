# bolt's laws. Each guarantee is one file under laws/, its prose on top and
# its quantified laws under it, proved by the file of the same name under
# proofs/; LAWS.bend and PROOF.bend only import them. A law file that says
# pending proves part of its guarantee, not all of it. The gate: the first
# line `bend PROOF.bend` prints is exactly `ALL PROOFS CHECK`. bend fails a
# proof that loads `@unsafe` or foreign code, imports included, so no proof
# imports a module holding a foreign effect: those take the effect as a
# service. Tests and fixtures are never evidence for a guarantee; what bolt
# cannot prove is said where it is assumed, on the code.
#
# These laws are what main.bend does with a Stop: main.bend only does what
# Args.out decides (laws/ states that decision for every argv). A text
# goes to its stream, and a code exits as it says: src/stop.bend's say and
# leave, which main.bend calls.
#
# The reasoning behind each guarantee is in docs/rfc/bolt-spec.md. It names
# the guarantees by the requirement IDs of docs/SPEC.md, the table these files
# replaced.
import Base
import ./laws/LeaveCode.bend as LeaveCode
import ./laws/LeaveZero.bend as LeaveZero
import ./laws/SayErr.bend as SayErr
import ./laws/SayLine.bend as SayLine
import ./laws/SayPage.bend as SayPage
import ./laws/CheckPrintsBendErrors.bend as CheckPrintsBendErrors
import ./laws/CliAcceptsDocumentedForms.bend as CliAcceptsDocumentedForms
import ./laws/CliDashHelp.bend as CliDashHelp
import ./laws/CliReadsArgumentsAfterProgram.bend as CliReadsArgumentsAfterProgram
import ./laws/CliVersion.bend as CliVersion
import ./laws/CliVersionExits.bend as CliVersionExits
import ./laws/CliVersionPrintsRelease.bend as CliVersionPrintsRelease
import ./laws/ConfigGradingDropsOff.bend as ConfigGradingDropsOff
import ./laws/ConfigGroupDefaultsHold.bend as ConfigGroupDefaultsHold
import ./laws/ConfigLevelsResolve.bend as ConfigLevelsResolve
import ./laws/ConfigNearestFileGrades.bend as ConfigNearestFileGrades
import ./laws/ConfigOptInStartsOff.bend as ConfigOptInStartsOff
import ./laws/ConfigUnknownLevelIsError.bend as ConfigUnknownLevelIsError
import ./laws/ConfigUnknownSettingsFound.bend as ConfigUnknownSettingsFound
import ./laws/ExitOnError.bend as ExitOnError
import ./laws/LastLineSummary.bend as LastLineSummary
import ./laws/LevelOwn.bend as LevelOwn
import ./laws/LinesInOrder.bend as LinesInOrder
import ./laws/OffRulesAreNotRun.bend as OffRulesAreNotRun
import ./laws/NoqaBare.bend as NoqaBare
import ./laws/NoqaBareText.bend as NoqaBareText
import ./laws/NoqaReportsStaleComments.bend as NoqaReportsStaleComments
import ./laws/NoqaSilencesNamedFindings.bend as NoqaSilencesNamedFindings
import ./laws/OutputCodesMapOneToOne.bend as OutputCodesMapOneToOne
import ./laws/OutputFindingFormatHolds.bend as OutputFindingFormatHolds
import ./laws/OutputUnreadablePathReported.bend as OutputUnreadablePathReported
import ./laws/PackageDirs.bend as PackageDirs
import ./laws/PackagesScoped.bend as PackagesScoped
import ./laws/ScopeConfigIsNeverLinted.bend as ScopeConfigIsNeverLinted
import ./laws/ScopeLawsGovernPackage.bend as ScopeLawsGovernPackage
import ./laws/ScopePackageRootsFound.bend as ScopePackageRootsFound
import ./laws/ImportPathsResolve.bend as ImportPathsResolve
import ./laws/PathsNameFiles.bend as PathsNameFiles
import ./laws/NamedFilesTakeTreeRoles.bend as NamedFilesTakeTreeRoles
import ./laws/PlannerAsksEachPathOnce.bend as PlannerAsksEachPathOnce
import ./laws/ConfigReadsSettings.bend as ConfigReadsSettings
import ./laws/TokenKindsNamed.bend as TokenKindsNamed
import ./laws/RulesNamedInCodeTable.bend as RulesNamedInCodeTable
import ./laws/BinderReadsBindingForms.bend as BinderReadsBindingForms
import ./laws/BinderFindsPositions.bend as BinderFindsPositions
import ./laws/OutlineLooksUpItems.bend as OutlineLooksUpItems
import ./laws/LexerCutsTokens.bend as LexerCutsTokens
import ./laws/TreeReadsStatements.bend as TreeReadsStatements
import ./laws/WordFindsNameAtCursor.bend as WordFindsNameAtCursor
import ./laws/RulesReadSignaturesAndLiterals.bend as RulesReadSignaturesAndLiterals
import ./laws/FindingsSayWhereAndWhat.bend as FindingsSayWhereAndWhat
import ./laws/RulesReadTokensAndChains.bend as RulesReadTokensAndChains
import ./laws/RewalkReadsNarrowAndWide.bend as RewalkReadsNarrowAndWide
import ./laws/LspRepliesListEveryEntry.bend as LspRepliesListEveryEntry
import ./laws/ScopeProjectRulesRunOnRoot.bend as ScopeProjectRulesRunOnRoot
import ./laws/ScopeRulesSeeTheirInputs.bend as ScopeRulesSeeTheirInputs
import ./laws/ScopeWalksWholeTree.bend as ScopeWalksWholeTree
import ./laws/SettingReportsUnknownNames.bend as SettingReportsUnknownNames
import ./laws/UnknownExact.bend as UnknownExact
import ./laws/WalkBfs.bend as WalkBfs
import ./laws/WantsTie.bend as WantsTie
import ./laws/UniqKeepsFirstOccurrences.bend as UniqKeepsFirstOccurrences
import ./laws/UnansweredAreOpenQuestions.bend as UnansweredAreOpenQuestions
import ./laws/ArmsReportCoveredNatArms.bend as ArmsReportCoveredNatArms
import ./laws/ArmsReportCoveredArms.bend as ArmsReportCoveredArms
import ./laws/CharsReportManyCharArms.bend as CharsReportManyCharArms
import ./laws/ClosedReportsBinderlessLaws.bend as ClosedReportsBinderlessLaws
import ./laws/CodeRulesIgnoreCommentsAndStrings.bend as CodeRulesIgnoreCommentsAndStrings
import ./laws/ConcatEither.bend as ConcatEither
import ./laws/ConcatPush.bend as ConcatPush
import ./laws/ConcatReportsAppendingRecursion.bend as ConcatReportsAppendingRecursion
import ./laws/ConcatReportsContinuationAppend.bend as ConcatReportsContinuationAppend
import ./laws/ConcatViaName.bend as ConcatViaName
import ./laws/DocReportsUndocumentedItems.bend as DocReportsUndocumentedItems
import ./laws/EagerReportsLoopsInPick.bend as EagerReportsLoopsInPick
import ./laws/EscapeReportsNulBeforeDigit.bend as EscapeReportsNulBeforeDigit
import ./laws/ExemptPathsYieldNoFindings.bend as ExemptPathsYieldNoFindings
import ./laws/ForeignReportsMissingBackend.bend as ForeignReportsMissingBackend
import ./laws/FromrevExempt.bend as FromrevExempt
import ./laws/FromrevReportsReversedStringBuild.bend as FromrevReportsReversedStringBuild
import ./laws/FuelReportsLiteralBudgets.bend as FuelReportsLiteralBudgets
import ./laws/HoleReportsEachTodo.bend as HoleReportsEachTodo
import ./laws/IndexReportsGetsInRecursion.bend as IndexReportsGetsInRecursion
import ./laws/InertConcatCont.bend as InertConcatCont
import ./laws/InertFromrev.bend as InertFromrev
import ./laws/InertTranscong.bend as InertTranscong
import ./laws/ImportReachIsClosed.bend as ImportReachIsClosed
import ./laws/LawNamesEveryItem.bend as LawNamesEveryItem
import ./laws/ParamReportsShortNames.bend as ParamReportsShortNames
import ./laws/PickReportsSelfCalls.bend as PickReportsSelfCalls
import ./laws/PickReportsBoundSearches.bend as PickReportsBoundSearches
import ./laws/PutReportsMapPutCalls.bend as PutReportsMapPutCalls
import ./laws/RewalkReportsRepeatedWalks.bend as RewalkReportsRepeatedWalks
import ./laws/RoleClosed.bend as RoleClosed
import ./laws/RoleClosedExempt.bend as RoleClosedExempt
import ./laws/RoleConcat.bend as RoleConcat
import ./laws/RoleDoc.bend as RoleDoc
import ./laws/RoleDocExempt.bend as RoleDocExempt
import ./laws/RoleEager.bend as RoleEager
import ./laws/RoleFromrev.bend as RoleFromrev
import ./laws/RoleFromrevExempt.bend as RoleFromrevExempt
import ./laws/RoleHole.bend as RoleHole
import ./laws/RoleHoleExempt.bend as RoleHoleExempt
import ./laws/RoleIndex.bend as RoleIndex
import ./laws/RoleLawFileNamed.bend as RoleLawFileNamed
import ./laws/RoleLawsNamed.bend as RoleLawsNamed
import ./laws/RoleNamedFirst.bend as RoleNamedFirst
import ./laws/RoleParam.bend as RoleParam
import ./laws/RoleParamExempt.bend as RoleParamExempt
import ./laws/RolePick.bend as RolePick
import ./laws/RoleProofNamed.bend as RoleProofNamed
import ./laws/RoleReached.bend as RoleReached
import ./laws/RoleFollowsImports.bend as RoleFollowsImports
import ./laws/RoleRewalk.bend as RoleRewalk
import ./laws/RoleStrict.bend as RoleStrict
import ./laws/RoleTail.bend as RoleTail
import ./laws/RoleThunk.bend as RoleThunk
import ./laws/ScopeConcatCont.bend as ScopeConcatCont
import ./laws/ScopeExemptionsFollowPaths.bend as ScopeExemptionsFollowPaths
import ./laws/SpaceReportsBlanksAndWidth.bend as SpaceReportsBlanksAndWidth
import ./laws/StrictReportsEagerSelfCalls.bend as StrictReportsEagerSelfCalls
import ./laws/StringsReportLongLiteralArms.bend as StringsReportLongLiteralArms
import ./laws/TailReportsNonTailCalls.bend as TailReportsNonTailCalls
import ./laws/ThunkReportsIgnoredSelfCallLambdas.bend as ThunkReportsIgnoredSelfCallLambdas
import ./laws/TranscongReportsTransCongChains.bend as TranscongReportsTransCongChains
import ./laws/UnusedReportsDeadBinders.bend as UnusedReportsDeadBinders
import ./laws/WrapReportsBrokenHeaderShape.bend as WrapReportsBrokenHeaderShape
import ./laws/LspAnswersEachRequestOnce.bend as LspAnswersEachRequestOnce
import ./laws/LspCheckerNeverRunsMain.bend as LspCheckerNeverRunsMain
import ./laws/LspDiagnosticsMatchCli.bend as LspDiagnosticsMatchCli
import ./laws/LspFramesCountBytes.bend as LspFramesCountBytes
import ./laws/LspNavigationUsesBinder.bend as LspNavigationUsesBinder
import ./laws/LspPositionsUseNegotiatedEncoding.bend as LspPositionsUseNegotiatedEncoding
import ./laws/LspPublishesOnDocumentEvents.bend as LspPublishesOnDocumentEvents
import ./laws/LspRequestsReadTheProtocol.bend as LspRequestsReadTheProtocol
import ./laws/LspKeepsRoleMarks.bend as LspKeepsRoleMarks
import ./laws/LspUnitsMatchCharsBelowAstral.bend as LspUnitsMatchCharsBelowAstral
import ./laws/ArrowTerm.bend as ArrowTerm
import ./laws/AttributeDef.bend as AttributeDef
import ./laws/BinderResolvesInnermostFirst.bend as BinderResolvesInnermostFirst
import ./laws/BinderIndexFindsItems.bend as BinderIndexFindsItems
import ./laws/DocFlagsAnswerAsLines.bend as DocFlagsAnswerAsLines
import ./laws/LexPositionsAreZeroBased.bend as LexPositionsAreZeroBased
import ./laws/LexRoundTripsText.bend as LexRoundTripsText
import ./laws/MarkedArrowTerm.bend as MarkedArrowTerm
import ./laws/OutlineListsTopLevelItems.bend as OutlineListsTopLevelItems
import ./laws/TreeKeepsEveryToken.bend as TreeKeepsEveryToken
import ./laws/EitherIsPick.bend as EitherIsPick
import ./laws/InertPrefix.bend as InertPrefix
import ./laws/LazyMatchesEagerCombinators.bend as LazyMatchesEagerCombinators
import ./laws/PrefixExempt.bend as PrefixExempt
import ./laws/PrefixReportsMatchingLength.bend as PrefixReportsMatchingLength
import ./laws/PrefixReportsTakeComparedToLiteral.bend as PrefixReportsTakeComparedToLiteral
import ./laws/PrefixSkipsOtherLengths.bend as PrefixSkipsOtherLengths
import ./laws/RolePrefix.bend as RolePrefix
import ./laws/RolePrefixExempt.bend as RolePrefixExempt
import ./laws/EmptyExempt.bend as EmptyExempt
import ./laws/EmptyReportsKeptTest.bend as EmptyReportsKeptTest
import ./laws/EmptySkipsUnkeptTest.bend as EmptySkipsUnkeptTest
import ./laws/RoleEmpty.bend as RoleEmpty
import ./laws/RoleEmptyExempt.bend as RoleEmptyExempt
import ./laws/InertEmpty.bend as InertEmpty
import ./laws/InertArmsCover.bend as InertArmsCover
import ./laws/EmptySkipsProofs.bend as EmptySkipsProofs
import ./laws/BlankReportsEmptyLiteralTest.bend as BlankReportsEmptyLiteralTest
import ./laws/BlankSkipsProofs.bend as BlankSkipsProofs
import ./laws/BlankExempt.bend as BlankExempt
import ./laws/RoleBlank.bend as RoleBlank
import ./laws/RoleBlankExempt.bend as RoleBlankExempt
import ./laws/InertBlank.bend as InertBlank
