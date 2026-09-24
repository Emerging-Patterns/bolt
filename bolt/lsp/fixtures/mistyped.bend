import Base

# a body that is not the type it declares: the checker's one error
def f(xx: U32) -> String:  # noqa: L001 fixture, ill-typed on purpose
  xx
