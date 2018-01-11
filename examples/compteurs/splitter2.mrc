// -----------------------------------------------------------------------------
// Type definitions and initial values
// -----------------------------------------------------------------------------

type process

type directions = enum {none, right, stop, down}

type pc = enum {pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9}

var process x
var bool y = false
var array(process, directions) rval = mk_array[process] (none)
var array(process, pc) pc = mk_array[process] (pc0)


var int alive = 0
var int countstop = 0
var int countdown = 0
var int countright = 0

// -----------------------------------------------------------------------------
// Transitions
// -----------------------------------------------------------------------------

transition spl0(process i)
require ( pc[i] = pc0 )
{
        alive := alive + 1;
        x := i;
        pc[i] := pc1;
}

transition spl1a(process i)
require ( pc[i] = pc1 )
require ( y = true )
{
        pc[i] := pc2;
}

transition spl1b(process i)
require ( pc[i] = pc1 )
require (y = false )
{
        pc[i] := pc3;
}

transition splright(process i)
require ( pc[i] = pc2 )
{
        countright := countright + 1;
        alive := alive - 1;
        rval[i] := right;
        pc[i] := pc7;
}

transition spl3(process i)
require ( pc[i] = pc3 )
{
        y := true;
        pc[i] := pc4;
}

transition spl4a(process i)
require ( pc[i] = pc4 )
require ( x = i )
{
        pc[i] := pc5;
}

transition spl4b(process i)
require ( pc[i] = pc4 )
require ( x != i )
{
        pc[i] := pc6;
}

transition splstop(process i)
require ( pc[i] = pc5 )
{
        countstop := countstop + 1;
        alive := alive - 1;
        rval[i] := stop;
        pc[i] := pc8;
}

transition spldown(process i)
require ( pc[i] = pc6 )
{
        countdown := countdown + 1;
        alive := alive - 1;
        rval[i] := down;
        pc[i] := pc9;
}

// -----------------------------------------------------------------------------
// Unsafe states
// -----------------------------------------------------------------------------

def bool two_stops =
        forall (process i, process j)
        (i != j && rval[i] = stop => rval[j] != stop)        

def bool cptstop = countstop <= 1

def bool safe1 = alive = 0 && countdown = 0 && countstop = 0 => countright <= 1

def bool safe2 = alive = 0 && countright = 0 && countstop = 0 => countdown <= 1

// -----------------------------------------------------------------------------
// Set Invariants (all these variables are counters, they can't be negative
// -----------------------------------------------------------------------------

def bool inv1 = alive >= 0

def bool inv2 = countstop >= 0

def bool inv3 = countright >= 0

def bool inv4 = countdown >= 0

def bool invar = inv1 && inv2 && inv3 && inv4

// -----------------------------------------------------------------------------
// Own invariants
// -----------------------------------------------------------------------------

def bool pcalive1 = 
        forall (process i) (
        pc[i] = pc1 || pc[i] = pc2 || pc[i] = pc3 || pc[i] = pc4 || pc[i] = pc5 || pc[i] = pc6 => alive >= 1)

def bool pcalive2 =
        forall (process i) (
        pc[i] = pc0 || pc[i] = pc7 || pc[i] = pc8 || pc[i] = pc9 => alive >= 0)

// -----------------------------------------------------------------------------
// Invariants inferred by Cubicle
// -----------------------------------------------------------------------------

def bool inv5 = forall (process i) (y = false => rval[i] != stop)
def bool inv6 = forall (process i) (y = false => pc[i] != pc4)
def bool inv7 = forall (process i) (y = false => pc[i] != pc6)
def bool inv8 = forall (process i) (y = false => pc[i] != pc2)

def bool invar2 = inv5 && inv6 && inv7 && inv8

// -----------------------------------------------------------------------------
// Goals
// -----------------------------------------------------------------------------

// goal g0 = invariant invar2
goal g0 = invariant (invar && pcalive1 && pcalive2)

// goal main = formula (invar2 => two_stops && cptstop && safe1 && safe1)