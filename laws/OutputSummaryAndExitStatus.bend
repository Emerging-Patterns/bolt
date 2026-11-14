# The last line is `clean` or `N errors, M warnings`, and the exit status is 1
# exactly when some graded finding is an error, counting the findings
# laws/OutputOrderIsFixed.bend prints.
#
# also rests on: laws/ExitOnError.bend, laws/LastLineSummary.bend
import Base
