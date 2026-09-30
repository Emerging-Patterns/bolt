# rule setting: a setting in a bolt.bend (a `def` whose body holds a string)
# whose name is neither a rule's slug nor a group, as the code table
# (src/codes.bend) lists them. Grading only looks names up, so such a setting
# sets nothing and fails open: `def wrp() -> String: "off"` leaves `wrap` at
# its group's level, and a retired name (`def quantify()`, `def shadow()`)
# does nothing at all. Rename it to the rule or group it meant, or delete it.
#
# A bolt.bend is read, never linted (BOLT-SCOPE-5), so this is not a per-file
# rule: the planner (src/lint/plan.bend) runs it once over each bolt.bend
# that grades a directory of the run, the first of that directory's
# candidates it read (BOLT-CFG-4), and reports each unknown setting at that
# bolt.bend's path and the line of its `def`, in file order, after the
# per-file findings and before the project rules'. It is graded by the
# bolt.bend it reports on, like any rule (`def setting() -> String: "off"`
# turns it off there). A noqa comment in a bolt.bend silences nothing, since
# the file is never read for marks. The editor does not run it (BOLT-LSP-4).
import Base
import ../../finding.bend as F
import ../../config.bend as Config

# each setting as a finding at the bolt.bend's path and its def's line
def found(ss: List<&2, Config.Setting>, +path: String) -> List<&2, F.Finding>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{Config.Setting{n, _w, line}, rest}:
      F.Finding{path, line, 0, 0, "setting", "`" ++ n ++ "` names no rule or group, so it sets nothing."}
        <> found(rest, path)

# the findings on a bolt.bend's text: one for each setting whose name is no
# rule or group, in file order
def check(+path: String, text: String) -> List<&2, F.Finding>:
  found(Config.unknown(Config.settings(text)), path)
