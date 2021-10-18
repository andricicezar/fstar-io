module Notes

(**
lift: IO -> IIO (Done - in IIO.Effect.fst)
lift: MIO -> MIIO (the lift from IO to IIO should work automatically)

export: IIO -> MIIO (Done: exportable_IIO)
export: IO -> MIIO (Done: exportable_IO - lift automatically to IIO,
                          and then use export: IIO -> MIIO)

import: MIIO -> IIO (Done: importable_MIIO_IIO)
import: MIO -> IIO (Done: importable_MIO_IIO) lift from MIO to MIIO,
                          and then import to IIO)

Not possible cases:
IIO -> IO
IIO -> MIO (the runtime checks can not be
           enforced statically because GetTrace is missing in IO)

IO -> MIO (the preconditions can not be enforced
           dynamically because GetTrace is missing in IO)

MIO -> IO (we can not enforce preconditions
           statically)

MIIO -> IO
MIIO -> MIO (Not possible because we can not get rid of GetTrace)
**)

