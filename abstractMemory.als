module examples/abstractMemory [Addr, Data] --parameters for opening this in another file

sig Memory{
	data: Addr ->lone Data --crucial point: in abstract model, not every address needs to be mapped from the get-go
}

/*this allows us to use '=' to compare different Memory sigs and ensure that they
evaluate to equal so long as their data mappings are equal*/
fact Canonicalize {
	no disj m,m': Memory| m.data = m'.data -- two memories are only different if their data mappings are different
}

pred init[m: Memory] { 
	no m.data -- initialize to empty mapping
}

pred write[m,m': Memory, a:Addr, d: Data]{
	m'.data = m.data ++ a->d --add/overwrite address a with the data d
}

//returns the stored data if there is one or else returns anything
pred read[m: Memory, a:Addr, d:Data]{
	let d' = m.data[a]| some d' implies d = d' -- if no a in data mapping, then the "some d'" fails, and an implication with a false pretense is always true, so no constriant on d
}

/*if you write something to an address,  reading at that same address
should produce the value you just wrote*/
assert WriteRead{
	all m, m': Memory, a:Addr, d1,d2: Data|
		write[m,m',a,d1] and read[m',a,d2] => d1 = d2
}

 //overwriting a with same data produces the same Memory
assert WriteIdempotent{
	all m,m',m'':Memory, a: Addr, d:Data|
		write[m,m',a,d] and write[m',m'',a,d] => m'=m''
}
