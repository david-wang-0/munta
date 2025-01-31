
import qualified Debug.Trace;

print s = Debug.Trace.trace s ();

printM s = Debug.Trace.traceM s;

