# Should the language server run on the GPU?

No. On the server's own pure work the GPU is slower than the CPU cores at
every batch size measured, from 1 request to 262,144 — by 2x to 5x on the
compute alone, and by a further ~150 ms per process for starting CUDA.

## What was measured

`request.bend` is what one hover costs the server apart from IO: parse the
JSON message, outline the document, find the word under the position, find its
item. `fold!(d, 0)` does that 2^d times under a `!` parallel call, split in two
per level, so **one binary** runs the identical code on the cores
(`--gpu off`) or on the GPU (`--gpu 4GB`); every lane printed the same
checksum. IO cannot run on the GPU at all (transport, files, the checker), so
this pure part is everything the GPU could take.

- *fold ms*: `IO.now()` around the fold, inside the process — compute only.
- *wall ms*: the whole process, which adds the runtime's start and CUDA's.
- Median of 3 runs, taken by hand.

To reproduce, build `request.bend` and run it once per depth and lane. The
binary reads `DEPTH` from the environment and prints its checksum, then the
fold's own milliseconds:

    bend bolt/lsp/bench/request.bend -o bin/bench-request
    DEPTH=18 ./bin/bench-request --gpu off --threads 1
    DEPTH=18 ./bin/bench-request --gpu off
    DEPTH=18 ./bin/bench-request --gpu 4GB

`bend` builds it directly rather than `ez build`, because `ez build` builds
the entry the ledger names and this is not that entry.

**`request.bend` does not build on bend 2.0.20.** It was written against
2.0.3, and 2.0.20 rejects the bare operators on line 46:

    - expected : a defined name
    - observed : U32../../../json/value.u32_or

So the table below is a record of what was measured, not something you can
re-run today without fixing that line first. The shell script that used to sit
here could not have run either: it would have reported `build failed`.

The *fold ms* column comes straight off that second line. The *wall ms*
column is the whole process, so it needs an external timer. The sweep and the
median used to be a shell script; they are three lines of whatever shell you
are sitting in, and nothing in bolt is built or gated on them.

Ryzen 9 5900X (12 cores, 24 threads), RTX 3060 12 GB (CUDA 12.5, idle before
each run; at 100% utilization during the GPU runs, the process listed by
`nvidia-smi`), Bend 2.0.3, clang 19.1.7, 2026-09-17.

## Results

| requests | fold ms: 1 core | all cores | GPU | GPU vs all cores | wall ms: all cores | GPU |
|---------:|----------------:|----------:|----:|-----------------:|-------------------:|----:|
| 1        | 0     | 0    | 20   | —     | 7    | 159  |
| 4        | 0     | 1    | 20   | 20x slower  | 9    | 163  |
| 16       | 2     | 2    | 23   | 11x slower  | 9    | 157  |
| 64       | 5     | 3    | 33   | 11x slower  | 10   | 172  |
| 256      | 19    | 4    | 22   | 5.5x slower | 12   | 166  |
| 1,024    | 73    | 11   | 34   | 3.1x slower | 16   | 178  |
| 4,096    | 286   | 29   | 61   | 2.1x slower | 41   | 207  |
| 16,384   | 1157  | 111  | 241  | 2.2x slower | 121  | 384  |
| 65,536   | 4586  | 400  | 1124 | 2.8x slower | 441  | 1275 |
| 262,144  | 18036 | 1555 | 4794 | 3.1x slower | 1560 | 4941 |

## Reading it

- **A language server answers one request at a time.** That is the first row:
  about 0.07 ms of compute on one core (18036 ms / 262,144), against a 20 ms
  floor for any `!` dispatch to the GPU — roughly 300x — before the 150 ms CUDA
  start a GPU-enabled server would pay at launch, and the VRAM it would hold
  beside LocalAI.
- **The gap does not close with scale.** At 262,144 requests the cores do
  169k requests/s and the GPU 55k. The ratio gets *worse* past 4,096, not
  better: this is not a fixed overhead being amortized.
- **Why.** The work is parsing: strings are linked lists of chars, every step
  is a branch on a constructor, and neighbouring leaves take different paths.
  Bend's guide says as much — the GPU wins on uniform numeric work
  (mandelbrot, nbody) and loses on divergent work (n-queens). core's
  `par/fold.bend` is the uniform kind, and there the GPU does win on this
  machine (2^32 leaves: 4.0 s against 5.3 s on all cores).
- **What the GPU does beat is one core**, from about 1,000 requests up (3.8x at
  262,144). So the honest claim is "slower than the cores", not "slow": were
  the choice a GPU or a single thread for bulk work, the GPU would be right.
- **What to use for bulk work** (indexing a workspace): the same parallel call
  without the `!`. All cores are 11.6x one core at 262,144 requests, with no
  start-up cost and no VRAM.

The server therefore stays a CPU binary, launched `--gpu off`.
