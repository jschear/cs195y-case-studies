module examples/cacheMemory[Addr, Data] -- paramterized over Addr and Data again

sig CacheSystem {
	main, cache: Addr -> lone Data -- this time has two mappings, one for main memory and one for the cache
}

pred init[c: CacheSystem] {
	no c.main + c.cache -- once again, no mapping at start
}

pred write[c, c': CacheSystem, a: Addr, d: Data] {
	c'.main = c.main -- no change in main memory
	c'.cache = c.cache ++ a->d --overwrite of cache at address
}

-- unlike the abstract example, this doesn't allow reads for addresses that don't have mappings
pred read[c: CacheSystem, a: Addr, d: Data] {
	some d
	d = c.cache[a] -- d is the data mapped to by a in the cache, there must be some d
}

pred load[c, c': CacheSystem] {
	some addrs: Addr |  -- for some set of addresses in main memory
		c'.cache = c.cache ++ addrs <: c.main -- overwrite the cache with the mappings from main memory
	c'.main = c.main -- main memory doesn't change
}

pred flush[c, c': CacheSystem] {
	some addrs: some c.cache.Data { -- for some set of addresses in the cache
		c'.main = c.main ++ addrs <: c.cache -- overwrite the mappings in main memory
		c'.cache = c.cache - addrs -> Data -- AND remove those mappings from the cache
	}
}

assert LoadNotObservable {
	all c, c', c'': CacheSystem, a1, a2: Addr, d1, d2, d3: Data |
		{
		read[c, a2, d2]
		write[c, c', a1, d1]
		load[c', c'']
		read[c'', a2, d3]
		} implies d3 = (a1 = a2 => d1 else d2)
}
check LoadNotObservable

/* incorrect load:
pred load[c, c': CacheSystem] { -- this lets the set of addresses contain some that map to data in both the cache and main memory
	some addrs: set Addr | c'.cache = c.cache ++ addrs <: c.main
	c'.main = c.main
} */

		
		
