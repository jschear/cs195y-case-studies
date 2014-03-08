module examples/hotel -- formalism. Does not get referenced anywhere else.
open util/ordering[Time] --The ordering of timesteps
open util/ordering[Key] -- The ordering of the keys (global but each lock has a subset of keys)

/** Sigs & Facts **/
sig Key,Time {}

sig Room{
	keys: set Key, -- the subset of the keys that belong to this room -- could a room have no Keys??
	currentKey: keys one ->Time -- injective relation of keys to time. No two keys in the same room map to the same time
}

fact DisjointKeySets{
	/*explanation: 
	left side: restricting keys to just the relation in Room (not Guest)
	right side: each key is mapped to by 0 or 1 rooms	*/
	Room <: keys in Room lone -> Key -- called a declaration formula
}

one sig FrontDesk{
	lastKey: (Room->lone Key) -> Time, -- last key for every room. *What is arity if there is no Key. Lone doesnt actuall matter
	occupant: (Room->Guest)-> Time -- who is in each room at a given time
}

sig Guest{
	// this relation is straighforward
	keys: Key->Time -- what is the implied multiplicity here (We think set of one->one mapping) ? could a guest have multiple keys 
}

/** State Changes **/
//this function returns the next key to be used for the room
// ks is called on room.keys
fun nextKey[k: Key, ks: set Key]: set Key {
	min[k.nexts & ks] -- k.nexts is the set of following keys
	//ks is set of keys for that room
	// min is therefore the lowest-order key in the set of keys for that room
}

pred init[t: Time]{
	no Guest.keys.t -- at the beginning no guest has a key
	no FrontDesk.occupant.t -- no occupants st the initial timestep
	all r: Room| FrontDesk.lastKey.t[r] = r.currentKey.t --frontdesk's list and rooms' list are staring at the same place
	--these keys are never actually used by guests
}

pred entry[t,t':Time, g: Guest, r: Room, k: Key]{
	k in g.keys.t --guest has key at time t 
	let ck = r.currentKey | -- ck is room's current key
		(k = ck.t and ck.t' = ck.t) or --k is the current key and the curr key does not change over the timestep. This is when someone is returning to a room they already have been in (not right after chekin)
		(k = nextKey[ck.t, r.keys] and ck.t' = k) -- the key is the next one and is chaging at the appropriate timestep. This is when someone is entering a room for the first time. 
	--frame conditions
	noRoomChangeExcept[t,t',r]	-- 	this is the only room that has a change at this time
	noGuestChangeExcept[t,t',none] -- no guests' keys are changing
	noFrontDeskChange[t,t'] --global list of occupants and last used keys is not changing
}

pred checkout[t, t': Time, g: Guest] {
	let occ = FrontDesk.occupant {
		some occ.t.g -- g has a room at time t (or multiple rooms?)
		occ.t' = occ.t - Room->g -- next list of occupants is the same as before sans all of g's rooms
	}
	FrontDesk.lastKey.t = FrontDesk.lastKey.t' -- the lastKey at the frontdesk doesn't change
	noRoomChangeExcept[t, t', none] -- no one is going into rooms
	noGuestChangeExcept[t, t', none] -- no guest's keys change
}

pred checkin[t, t': Time, g: Guest, r: Room, k: Key] {
	g.keys.t' = g.keys.t + k -- guest gets one key (guest could have existing rooms)
	let occ = FrontDesk.occupant {
		no occ.t[r] -- there's no one in the room at time t
		occ.t' = occ.t + r->g -- record g as occupant of room r
	}
	let lk = FrontDesk.lastKey {
		lk.t' = lk.t ++ r-> k -- update frontdesk's record of the room's last key (override to replace old lastkey)
		k = nextKey[lk.t[r], r.keys] -- this is how the frontdesk knows what the lastkey is; lk.t[r] is the room's key at time t
	}
	noRoomChangeExcept[t, t', none] -- no one is going into rooms
	noGuestChangeExcept[t, t', g] -- no guest's keys change other than g's
}

-- none of the FrontDesk's fields change
pred noFrontDeskChange[t, t': Time] {
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	FrontDesk.occupant.t = FrontDesk.occupant.t'
}

-- no room's currentKey changes
pred noRoomChangeExcept[t, t': Time, rs: set Room] {
	all r: Room - rs | r.currentKey.t = r.currentKey.t'
}

-- no Guest's KEYS change
pred noGuestChangeExcept[t, t': Time, gs: set Guest] {
	all g: Guest - gs | g.keys.t = g.keys.t'
}


/** Traces **/
fact Traces {
	first.init -- how do we know that this is Time's first, not keys?
	all t: Time - last | let t' = t.next | -- between each timestep, either an entry, a checkin, or a checkout occurs
		some g: Guest, r: Room, k: Key |
			entry[t, t', g, r, k]
			or checkin[t, t', g, r, k]
			or checkout[t, t', g]
	-- we don't need to make sure only one of these happens because the frame conditions ensure it
}

assert NoBadEntry {
	all t: Time, r: Room, g: Guest, k: Key |
		let o = FrontDesk.occupant.t[r] | -- whenever a guest g enters a room, that guest must be listed as an occupant of the room
			entry[t, t.next, g, r, k] and some o => g in o -- o is set of room's occupants, g is the guest that enters
}

fact noIntervening {
	all t: Time - last | let t' = t.next , t'' = t'.next |
		all g: Guest, r: Room, k: Key |
			checkin[t, t', g, r, k] => (entry[t', t'', g, r, k] or no t'') -- either the checkin was the last action, or the guest immediately enters the room
	-- q: is this realistic?
}

run {}
