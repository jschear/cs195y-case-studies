module examples/fixedSizeMemory_H [Addr, Data] --parameters for opening this in another file
open case_studies/fixedSizeMemory[Addr, Data] as memory

-- same as fixedSize, keeps track of which have been written
sig Memory_H extends memory/Memory {
	unwritten: set Addr
}

pred init[m: Memory_H] {
	memory/init[m]
	m.unwritten = Addr
}

pred read[m: Memory_H, a: Addr, d: Data] {
	memory/read[m, a, d]
}

pred write[m, m': Memory_H, a: Addr, d: Data] {
	memory/write[m, m', a, d]
	m'.unwritten = m.unwritten - a
}
