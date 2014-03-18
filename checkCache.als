module examples/checkCache[Addr, Data]

open case_studies/cacheMemory[Addr, Data] as cache
open case_studies/abstractMemory[Addr, Data] as amemory

-- the abstract model's memory is the main memory overridden with the cache in the concrete model
fun alpha[c: CacheSystem]: Memory {
	{m: Memory | m.data = c.main ++ c.cache}
}

run {}

-- concrete operation on CacheSystems implies the corresponing operation of Memorys returned by the abstraction function
assert ReadOK {
	all c: CacheSystem, a: Addr, d: Data, m: Memory |
		cache/read[c, a, d] and m = alpha[c] implies amemory/read[m, a, d]
}
check ReadOK

assert WriteOK {
	all c, c': CacheSystem, a: Addr, d: Data, m, m': Memory |
		cache/write[c, c', a, d] and m = alpha[c] and m' = alpha[c']  implies amemory/write[m, m', a, d]
}
check WriteOK

-- same as above, but there is no corresponding operation so we check them against the operation that does nothing
assert LoadOK {
	all c, c': CacheSystem, m, m': Memory | cache/load[c, c'] and m = alpha[c] and m' = alpha[c] implies m = m'
}
check LoadOK

assert FlushOK {
	all c, c': CacheSystem, m, m': Memory | cache/flush[c, c'] and m = alpha[c] and m' = alpha[c] implies m = m'
}
check FlushOK
