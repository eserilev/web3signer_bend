# Proofs of the core laws (L10): the plan of src/core.bend writes before it
# grants, and the state after a step is the written events applied.
import Base
import ../src/store.bend as St
import ../src/core.bend as Co
import ../spec/core.bend as Core

def write_first_of(o: St.Outcome) -> {Core.write_first(Co.Plan.of(o)) == True{} : Bool}:
  match o:
    case St.Refuse{c, why}:
      {==}
    case St.Sign{es}:
      match es:
        case Nil{}:
          {==}
        case Con{e, rest}:
          {==}

def app_nil(xs: List<&2, St.LogEvent>) -> {List.append(&2, St.LogEvent, xs, []) == xs : List<&2, St.LogEvent>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %app_nil(t) : {Con{x, List.append(&2, St.LogEvent, t, [])} == Con{x, _} : List<&2, St.LogEvent>}
      {==}

def log_of(+s: St.Store, o: St.Outcome) -> {St.Store.after(s, o) == St.Store.apply_all(Co.Plan.writes(Co.Plan.of(o)), s) : St.Store}:
  match o:
    case St.Refuse{c, why}:
      {==}
    case St.Sign{es}:
      match es:
        case Nil{}:
          {==}
        case Con{+e, +rest}:
          %Equal.sym(List<&2, St.LogEvent>, List.append(&2, St.LogEvent, Con{e, rest}, []), Con{e, rest}, app_nil(Con{e, rest}))
            : {St.Store.apply_all(Con{e, rest}, s) == St.Store.apply_all(_, s) : St.Store}
          {==}
