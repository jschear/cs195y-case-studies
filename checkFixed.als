module examples/checkFixedSize [Addr, Data]
open case_studies/fixedSizeMemory_H [Addr,Data] as fmemory
open case_studies/abstractMemory [Addr,Data] as amemory

//abstraction function (written as pred)
//written as pred just to demonstrate different style
//also, alloy fun is not necessarily a function in this sense, as it could return a set of things
pred alpha[fm: fmemory/Memory, am: amemory/Memory]{
	am.data = fm.data - (fm.unwritten->Data) -- abstract memory is fixed sized's memory less those addresses that have not yet been written
}

//assert that they are initialized the same
//both should have empty mappings since all addresses will not have been written to 
//we did not do this in the cache case because it was trivial
assert initOK{
	all fm: fmemory/Memory, am: amemory/Memory|
		fmemory/init[fm] and alpha[fm,am]
			=> amemory/init[am]
}check initOK for 3 but 1  fmemory/Memory, 1 amemory/Memory

//self-explanatiory: op + abstraction on fixed implies op on abstract
assert readOK{
	all fm: fmemory/Memory,a:Addr, d: Data, am: amemory/Memory|
		fmemory/read[fm,a,d] and alpha[fm,am]
			=> amemory/read[am,a,d]
}check readOK


assert writeOK{
	all fm,fm': fmemory/Memory,a:Addr, d: Data, am,am': amemory/Memory|
		fmemory/write[fm,fm',a,d] and alpha[fm,am] and alpha[fm',am']
			=> amemory/write[am,am',a,d]
}check writeOK
