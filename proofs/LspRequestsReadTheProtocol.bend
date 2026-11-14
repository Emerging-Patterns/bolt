# proofs of laws/LspRequestsReadTheProtocol.bend: case by case, or by
# evaluation
import Base
import ../src/lsp/enc.bend as Enc
import ../src/lsp/server.bend as Server
import ../laws/LspRequestsReadTheProtocol.bend as Laws

def Laws.method_by_wire_name(mm):
  match mm:
    case Server.MInitialize{}:
      {==}
    case Server.MShutdown{}:
      {==}
    case Server.MExit{}:
      {==}
    case Server.MOpen{}:
      {==}
    case Server.MChange{}:
      {==}
    case Server.MSave{}:
      {==}
    case Server.MClose{}:
      {==}
    case Server.MHover{}:
      {==}
    case Server.MDefinition{}:
      {==}
    case Server.MSymbols{}:
      {==}
    case Server.MCompletion{}:
      {==}
    case Server.MReferences{}:
      {==}
    case Server.MRename{}:
      {==}
    case Server.MSemantic{}:
      {==}
    case Server.MOther{}:
      {==}

def Laws.request_method_field(_name, _id, _params):
  {==}

def Laws.request_id_field(_name, _id, _params):
  {==}

def Laws.request_uri_field(_uri, _pos):
  {==}

def Laws.request_line_field(_doc, _line, _character):
  {==}

def Laws.request_character_field(_doc, _line, _character):
  {==}

def Laws.encoding_wire_names(ee):
  match ee:
    case Enc.Utf16{}:
      {==}
    case Enc.Utf32{}:
      {==}

def Laws.legend_wire_names(n):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n+_:
      {==}

def Laws.encoding_reads_params(_msg, _ee):
  {==}

def Laws.rename_refuses_a_foreign_name(_cc, _at, _uri, _name, _new):
  {==}
