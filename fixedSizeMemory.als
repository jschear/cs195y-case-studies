module examples/fixedSizeMemory [Addr, Data] --parameters for opening this in another file

sig Memory {
	data: Addr -> one Data -- every Addr is mapped to one Data
}

-- note, no canonicalize

pred init[m: Memory] {} -- everything is mapped at the beginning!

pred write[m,m': Memory, a:Addr, d: Data]{
	m'.data = m.data ++ a->d --add/overwrite address a with the data d
}

pred read[m: Memory, a:Addr, d:Data]{
	d = m.data[a] -- could still be arbitrary value if address hasn't been written to yet
} 
