# transport: an effect service: one message body in, one out. H is the
# implementation's handle state; it is affine, so every call hands it back.
import Base

# effect service over a handle H: receive a body, send a body, each handing the
# handle back
type Transport<-H: Type> is Type:
  Transport{recv: H -> IO(H & Maybe<&2, String>), send: H -> String -> IO(H)}

# the next message's body; None when the peer is gone
def recv(-H: Type, tt: Transport<H>, hh: H) -> IO(H & Maybe<&2, String>):
  Transport{r, s} = tt
  r(hh)

# a body, through a transport
def send(-H: Type, tt: Transport<H>, hh: H, body: String) -> IO(H):
  Transport{r, s} = tt
  s(hh, body)
