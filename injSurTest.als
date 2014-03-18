one sig Rel{
	map: A one-> B
}

sig A{}

sig B{}

assert injective{
	all a,a': A|all b:B| a->b in Rel.map and a'->b in Rel.map implies a = a'
}check injective for 8

assert surjective{
	Rel.map[A] = B
}check surjective for 8


run {}
