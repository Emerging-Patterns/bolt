# transport: an effect service: one message body in, one out. H is the
# implementation's handle state; it is affine, so every call hands it back.
import Base

type Transport<-H: Type> is Type:
  Transport{recv: H -> IO(H & Maybe<&2, String>), send: H -> String -> IO(H)}

# the next message's body; None when the peer is gone
def recv(-H: Type, t: Transport<H>, h: H) -> IO(H & Maybe<&2, String>):
  Transport{r, s} = t
  r(h)

def send(-H: Type, t: Transport<H>, h: H, body: String) -> IO(H):
  Transport{r, s} = t
  s(h, body)
