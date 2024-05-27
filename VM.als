// Interpreter:
one sig Interpreter
{
	var stack_ :  seq Frames
}

var sig Frames
{
	var callee_ : one MemorySlot,
	var locals_ : set MemorySlot
}
pred Check[f:Frames] {
	f.callee_ in Functions
}
fact FrameRestrictions {
	always all f : Frames | Interpreter.stack_.idxOf[f] != none
}

// GC:
one sig GC
{
	regions_ : disj seq Region
} {
	always {not regions_.hasDups} and {#regions_ = 2}
}

// The whole memory is separated by consequent regions.
// The first region is the youngest and the last is the oldest.
sig Region {
	var slots_: set MemorySlot
} 
fact RegionConfig {
	always all r : Region | #r.slots_ = 2
}

// A model of memory range that  each HeapObject occupy.
// For simplicity, its size is out of concern.
abstract var sig MemorySlot {}

var sig HeapObjects extends MemorySlot {}
var sig FreeSlots extends MemorySlot{} {FreeSlots + HeapObjects = MemorySlot}

var sig Functions extends HeapObjects
{
	var this_: lone MemorySlot
}
pred Check[f:Functions] {
	f.this_ in Maps
}
var sig Maps extends HeapObjects
{
	var elems_: set MemorySlot
}
var sig Strings extends HeapObjects {}
fact {
	always Functions + Maps + Strings = HeapObjects
}

fact MemorySlotRestrictions {
	// All Regions belong to the GC
	always all r : Region | GC.regions_.idxOf[r] != none
	// Slot is always belongs to exactly one Region
	always all ms : MemorySlot | one r : Region | ms in r.slots_ 
}

pred NoDangling {
	all f : Frames {
		f.locals_ in HeapObjects
		f.callee_ in HeapObjects
	}
	all f : Functions {
		f.this_ in HeapObjects
	}
	all m : Maps {
		m.elems_ in HeapObjects
	}
}


// Helpers
pred inv [f: Frames] {
	f.locals_' = f.locals_
	f.callee_' = f.callee_
}

pred inv [r: Region] {
	r.slots_' = r.slots_
}
pred inv [f: Functions] {
	f.this_' = f.this_
}

pred inv [m: Maps] {
	m.elems_' = m.elems_
}

// Main operations
pred Init {
	// 'main' function object:
	#Frames = 1
	#Frames.locals_ = 0
	Check[Frames]
	Check[Functions]
	one Functions
	one HeapObjects
	NoDangling
	Functions in GC.regions_.first.slots_
	// 'main' is exactly in the first region:
	//	all vr : Vregs | !IsDangling[vr]
}

pred Noop_impl {
	MemorySlot' = MemorySlot
	FreeSlots' = FreeSlots
	Maps' = Maps
	Frames' = Frames
	Interpreter.stack_' = Interpreter.stack_
	Region'.slots_'  = Region.slots_
	all r : Region | inv[r]
	all f : Frames | inv[f]
}

// 'Mutex' to allow exactly one operation per state change:
var sig NextOp_ {}
var sig Call_ extends NextOp_ {}
fact {
	always one NextOp_
}

pred Call_Impl {
	NextOp_ = Call_

	MemorySlot' = MemorySlot
	FreeSlots' = FreeSlots
	Maps' = Maps

	//one f0 : Frames' | not f0 in Frames

	Region'.slots_'  = Region.slots_

	all r : Region | inv[r]
	all f : Frames | inv[f]
}

pred Trans {
	always  Call_Impl //or Noop_impl
}

pred Simulate {
	Init and always Trans
}

run {Simulate} for  20 but 4..4 steps 
