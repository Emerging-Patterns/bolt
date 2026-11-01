# Output order is read failures, then per-file findings in file-list order and
# `Rules.on` order, then `setting`'s findings (C011), then `coverage`'s,
# less the findings a noqa comment silences
# (laws/NoqaSilencesNamedFindings.bend), then `noqa`'s findings (S005) in file-list order.
#
# also rests on: laws/LinesInOrder.bend
import Base


