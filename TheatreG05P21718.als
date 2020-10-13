open util/ordering[Time]	

sig Time{}

//=================
//  Pre-defined Sets
//=================

sig CLIENT {}
sig THEATRE {}
sig PLAY {}
sig NAME {}
sig EMAIL {}
sig PERFORMANCE {}
sig RESERVATION {}


//================
// Instances
//================

sig Client extends CLIENT {  //R1	
	name: one NAME, //R2
	email: EMAIL one->Time, //R2
	
}

sig Theatre extends THEATRE {  //R9
	number_of_seats: Int one->Time, //R10
}

sig Play extends PLAY {  //R13
	duration: one Int, 
}

sig Performance extends PERFORMANCE {  //R15	
	play: one PLAY, //R16
	theatre: one THEATRE, //R16
	begin_time: one Int, //R16
	end_time: one Int, //R16
	available_seats: Int one -> Time, 
}

sig Reservation extends RESERVATION {  	
	client: one CLIENT, //R21
	num_reserved_seats: Int one->Time, //R21 
	performance: one PERFORMANCE, //R21
}


//================
// Theatre registered
//================	
 
one sig ClientsRegistered {clients: Client->Time}

one sig ClientsBanned {clients: Client->Time}

one sig TheatresRegistered {theatres: Theatre->Time}

one sig PlaysRegistered {plays: Play->Time}

one sig PerformancesRegistered {performances: Performance->Time}

one sig ReservationsRegistered {reservations: Reservation->Time}

//================
// Initialization
//================

pred init[t: Time] {

	no ClientsRegistered.clients.t //R7
	no ClientsBanned.clients.t //R8
	no TheatresRegistered.theatres.t //R11
	no PlaysRegistered.plays.t //R14
    no PerformancesRegistered.performances.t //R20
	no ReservationsRegistered.reservations.t
}

//=====================
// Unaltered states
//=====================

pred unalteredClientsRegistered [t, t': Time]{
	ClientsRegistered.clients.t' = ClientsRegistered.clients.t
}

pred unalteredClientsBanned [t, t': Time]{
	ClientsBanned.clients.t' = ClientsBanned.clients.t
}

pred unalteredTheatresRegistered [t, t': Time]{
	TheatresRegistered.theatres.t' =TheatresRegistered.theatres.t
}

pred unalteredPlaysRegistered [t, t': Time]{
	PlaysRegistered.plays.t' = PlaysRegistered.plays.t
}

pred unalteredPerformancesRegistered [t, t': Time]{
	PerformancesRegistered.performances.t' = PerformancesRegistered.performances.t
}

pred unalteredReservationsRegistered [t, t': Time]{
	ReservationsRegistered.reservations.t' = ReservationsRegistered.reservations.t
}

//================
// Operations - Client
//================

pred addClient[c: Client, t, t': Time]{
	let cr = ClientsRegistered.clients{
		let cbanned = ClientsBanned.clients{
			!(c in cr.t) //R1 R6
			!(c in cbanned.t) //R5 R6
			all clients : cr.t | c.email != clients.email //R3
			cr.t' = cr.t + c

			//Not changed
			all cli : cr.t | cli.email.t' = cli.email.t
	
		}
	}
	unalteredTheatresRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

pred removeClient[c: Client, t, t': Time]{
	all reservation : ReservationsRegistered.reservations.t | reservation.client != c  //R24
	let cr = ClientsRegistered.clients{
		let cbanned = ClientsBanned.clients{ 
			!(c in cbanned.t) //R6
			c in cr.t //R4 R6
			cr.t' = cr.t - c
		
			//Not changed
			all cli : cr.t' | cli != c => cli.email.t' = cli.email.t
		}
	}
	unalteredTheatresRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

pred banClient[c: Client, t, t': Time]{ //R5
	let cr = ClientsRegistered.clients{
		let cbanned = ClientsBanned.clients{ 
			let rr = ReservationsRegistered.reservations{
				(c in cr.t) //R6
				!(c in cbanned.t) //R6
				
		 	    all reservation : ReservationsRegistered.reservations.t | reservation.client = c => reservation.performance.available_seats.t' =	add[reservation.performance.available_seats.t, reservation.num_reserved_seats.t] // R26
				rr.t' = rr.t - client.c				

				cr.t' = cr.t - c
				cbanned.t'= cbanned.t + c
			
				//Not changed
				all cli : cr.t' | cli != c => cli.email.t' = cli.email.t
				all reservation : ReservationsRegistered.reservations.t | reservation.client != c => reservation.performance.available_seats.t' = reservation.performance.available_seats.t and  rr.t' = rr.t
			}
		}
	}
	unalteredTheatresRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
}
pred upgradeClient[c: Client, e:EMAIL, t, t' : Time]{
	let cr = ClientsRegistered.clients{
		let cbanned = ClientsBanned.clients{ 
			c in cr.t //R6
			!(c in cbanned.t) //R6 
			all clients : cr.t | e != clients.email.t 
			c.email.t' = e 

			//Not changed
			cr.t - c = cr.t' - c
			c in cr.t'
			all cli : cr.t' | cli != c => cli.email.t' = cli.email.t
		}
	}
	unalteredTheatresRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

//================
// Operations - Theatre
//================

pred addTheatre[x: Theatre, t, t': Time]{
	let tr = TheatresRegistered.theatres{
		!(x in tr.t) //R9
		(x.number_of_seats.t > 0)
		tr.t' = tr.t + x
		
		 x.number_of_seats.t' = x.number_of_seats.t 

		//Not changed
		all th : tr.t |  th.number_of_seats.t' = th.number_of_seats.t 
	}
	unalteredClientsRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

pred updateTheatre[x: Theatre, n: Int, t, t': Time]{
	let tr = TheatresRegistered.theatres {
		x in tr.t
		x.number_of_seats.t' = n
		tr.t - x = tr.t' - x
		x in tr.t'
		
		all performance :  PerformancesRegistered.performances.t| performance.theatre = x => performance.available_seats.t' = x.number_of_seats.t 

		//Not changed
		all th : tr.t' | th != x => th.number_of_seats.t' = th.number_of_seats.t
	}
	unalteredClientsRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

pred removeTheatre[x: Theatre, t, t': Time]{
	all p : PerformancesRegistered.performances.t | p.theatre != x  //R27
	let tr = TheatresRegistered.theatres {
		x in tr.t //R12
		tr.t' = tr.t - x

		//Not changed
		all th : tr.t' | th != x => th.number_of_seats.t' = th.number_of_seats.t 
	}

	unalteredClientsRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

//================
// Operations - Play
//================

pred addPlay[p: Play, t, t': Time]{
	let pr = PlaysRegistered.plays{
		!(p in pr.t) //R13
		p.duration > 1
		pr.t' = pr.t + p	

	}
	unalteredTheatresRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

//================
// Operations - Performance
//================

pred addPerformance[p: Performance, t, t': Time]{
	let pr = PerformancesRegistered.performances{
		let playr = PlaysRegistered.plays{ 
			let tr = TheatresRegistered.theatres{ 	
				!(p in pr.t) //R15
				p.play in playr.t //R28
				p.theatre in tr.t //R29
				
				p.begin_time > 0
							
				add[p.begin_time, p.play.duration]  < p.end_time //R17
			    
				all performance : pr.t | !(performance.begin_time < p.end_time and p.begin_time < performance.end_time) //R19
			
				p.available_seats.t' = p.theatre.number_of_seats.t
			
				pr.t' = pr.t + p	
				
				//Not changed
				all performance : pr.t' | performance.available_seats.t' = performance.available_seats.t 
				all performance : pr.t' | performance.theatre.number_of_seats.t' = performance.theatre.number_of_seats.t
			}
		}
	}
	unalteredTheatresRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

pred cancelPerformance[p: Performance, t, t': Time]{ //R18
	let pr = PerformancesRegistered.performances{
		let rr = ReservationsRegistered.reservations{		
			p in pr.t //R18
			pr.t' = pr.t - p
		
			all reservation : ReservationsRegistered.reservations.t | reservation.performance = p => reservation.performance.available_seats.t' =	add[reservation.performance.available_seats.t, reservation.num_reserved_seats.t] 
			rr.t' = rr.t - performance.p
			
			//Not changed
			all performance : pr.t' | performance != p => performance.available_seats.t' = performance.available_seats.t 
			all performance : pr.t' | performance.theatre.number_of_seats.t' = performance.theatre.number_of_seats.t 
			all reservation : ReservationsRegistered.reservations.t | reservation.performance != p => reservation.performance.available_seats.t' =	reservation.performance.available_seats.t
			rr.t' = rr.t
		}
	}
	unalteredTheatresRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredClientsBanned [t, t']
}

//================
// Operations - Reservations
//================

pred makeReservation[r: Reservation, t, t': Time]{
	let rr = ReservationsRegistered.reservations {
		let cr = ClientsRegistered.clients {
			let pr = PerformancesRegistered.performances {
				let cbanned = ClientsBanned.clients{
					!(r in rr.t)
					!(r.client in cbanned.t)
					r.client in cr.t //R30
					r.performance in pr.t //R31				
				
					all reservation : rr.t | r.performance = reservation.performance => sum(reservation.num_reserved_seats.t) < r.performance.available_seats.t //R25

					r.performance.available_seats.t' = sub[r.performance.available_seats.t, r.num_reserved_seats.t]
					rr.t' = rr.t + r
					
						
					all reservation : rr.t' | reservation.performance != r.performance =>  reservation.performance.available_seats.t' = reservation.performance.available_seats.t 
					all clients : ClientsRegistered.clients.t' | clients.email.t' = clients.email.t  
					all reservation : rr.t' | reservation != r => reservation.num_reserved_seats.t' = reservation.num_reserved_seats.t 
				}
			}
		}
	}
	unalteredTheatresRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredClientsBanned [t, t']
}

pred updateReservation[r: Reservation, n: Int, t,t':Time]{
 	let rr = ReservationsRegistered.reservations{
		r in rr.t
		n > 0
		r.performance.available_seats.t' =sub[add[r.performance.available_seats.t, r.num_reserved_seats.t],n]
		r.num_reserved_seats.t'=n

		all reservation : rr.t' | reservation.performance != r.performance =>  reservation.performance.available_seats.t' = reservation.performance.available_seats.t 
		all reservation : rr.t' | reservation.client.email.t' = reservation.client.email.t
		all reservation : rr.t' | reservation != r => reservation.num_reserved_seats.t' = reservation.num_reserved_seats.t 
	}
	unalteredTheatresRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredReservationsRegistered [t, t']
	unalteredClientsBanned [t, t']
}

pred cancelReservation[r: Reservation, t,t':Time]{ //R22
 	let rr = ReservationsRegistered.reservations{
		r in rr.t
		r.performance.available_seats.t' =	add[r.performance.available_seats.t, r.num_reserved_seats.t] //R23
		rr.t' = rr.t - r

		all reservation : rr.t' | reservation.performance != r.performance =>  reservation.performance.available_seats.t' = reservation.performance.available_seats.t 
		all clients : ClientsRegistered.clients.t' | clients.email.t' = clients.email.t 
		all reservation : rr.t' | reservation != r => reservation.num_reserved_seats.t' = reservation.num_reserved_seats.t 
	}
	unalteredTheatresRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredPlaysRegistered [t, t']
	unalteredPerformancesRegistered [t, t']
	unalteredClientsBanned [t, t']
}


//================
// Begin
//================

fact traces {
	init[first]
	all t: Time-last | let t'=t.next |
		some c: Client, th: Theatre, pl: Play, p: Performance, r: Reservation, e: EMAIL,  n: Int | 
			addClient[c, t, t'] or
			removeClient[c, t, t'] or
			banClient[c, t, t']or
			upgradeClient[c, e, t, t']or
			addTheatre[th, t,t'] or
			updateTheatre[th, n, t, t'] or
			removeTheatre[th, t, t'] or
			addPlay[pl, t, t'] or
			addPerformance[p, t, t'] or
			cancelPerformance[p, t, t'] or
			makeReservation[r, t, t'] or
			updateReservation[r, n, t, t'] or
			cancelReservation[r, t, t'] 
}

run addClient
run removeClient
run banClient
run addTheatre
run updateTheatre
run removeTheatre
run addPlay
run addPerformance for 4
run cancelPerformance for 4 
run makeReservation for 6
run updateReservation for 6
run cancelReservation for 6

//================
// Asserts
//================

//R1
assert everyClientMayRegister{
	all t: Time, c: Client, cr: ClientsRegistered.clients  | let t' = t.next | addClient[c, t, t'] => c in ClientsRegistered.clients.t' and c not in cr.t	 
}
check everyClientMayRegister for 10

//R2
assert everyClientHasNameAndEmail{
	all c:ClientsRegistered.clients.Time | c.name in NAME and c.email.Time in EMAIL
}
check everyClientHasNameAndEmail for 10

//R3
assert everyEmailIsUnique{   
	all t: Time, i, j: ClientsRegistered.clients.t | i.email = j.email => i = j
}
check everyEmailIsUnique for 10

//R4
assert onlyRegisteredClientsCanBeRemoved{   
	all t: Time, c : Client | let t' = t.next | removeClient[c,t,t'] => c not in ClientsRegistered.clients.t'
}
check onlyRegisteredClientsCanBeRemoved for 10

//R5
assert bannedClientsCantBeAdded{
	all t: Time, i: Client | let t' = t.next | banClient[i, t, t'] => !addClient[i, t, t']
}
check bannedClientsCantBeAdded for 10

//R6	
assert intersectionBetweenBannedAndRegisteredIsEmpty{
	all t: Time, c1: ClientsRegistered.clients.t, c2: ClientsBanned.clients.t | c1!=c2 
}
check intersectionBetweenBannedAndRegisteredIsEmpty for 10

//R7
assert noClientsRegAtBeg{
	no ClientsRegistered.clients.first
}
check noClientsRegAtBeg for 10

//R8
assert noBannedClientsInTheBeggining{
	no ClientsBanned.clients.first
}
check noBannedClientsInTheBeggining for 10

//R9
assert everyTheatreMayRegister{
	all t: Time, th: Theatre, thr: TheatresRegistered.theatres  | let t' = t.next | addTheatre[th, t, t'] => th in TheatresRegistered.theatres.t' and th not in thr.t	 
}
check everyTheatreMayRegister for 10

//R10
assert theatresHaveNumberOfSeats{
	all t: Time, th: TheatresRegistered.theatres.t | #th.number_of_seats.t = 1
	all t: Time, th: Theatre | let t' = t.next | addTheatre[th, t, t'] => th.number_of_seats.t > 0
}
check theatresHaveNumberOfSeats for 10

//R11
assert noTheatresRegAtBeg{
	no TheatresRegistered.theatres.first
}
check noTheatresRegAtBeg for 10

//R12
assert removeOnlyRegTheatre {  
	all t: Time, th:Theatre| let t' = t.next | removeTheatre[th,t, t'] => th in TheatresRegistered.theatres.t
}
check removeOnlyRegTheatre for 10

//R13
assert everyPlayMayRegister{
	all t: Time, p: Play, pr: PlaysRegistered.plays  | let t' = t.next | addPlay[p, t, t'] => p in PlaysRegistered.plays.t' and p not in pr.t	 
}
check everyPlayMayRegister for 10

//R14
assert noPlayRegAtBeg{
	no PlaysRegistered.plays.first
}
check noPlayRegAtBeg for 10

//R15
assert everyPerformancesMayRegister{
	all t: Time, p: Performance, pr: PerformancesRegistered.performances  | let t' = t.next | addPerformance[p, t, t'] => p in PerformancesRegistered.performances.t' and p not in pr.t	 
}
check everyPerformancesMayRegister for 10

//R16
assert performanceHasIDPlayTheatreBeginEnd{
	all t: Time, p: Performance | p.play in PLAY and p.theatre in THEATRE and p.begin_time in Int and p.end_time in Int and p.available_seats.t in Int 
}
check performanceHasIDPlayTheatreBeginEnd for 10

//R17
assert performanceHasCorrectEndingTime{
	all t: Time, p: PerformancesRegistered.performances.t | add[p.begin_time, p.play.duration] < p.end_time
}
check performanceHasCorrectEndingTime for 10

//R18
assert performanceCanBeCancelled{
	all t: Time, p: PerformancesRegistered.performances.t | let t' = t.next | cancelPerformance[p, t, t']  => p not in PerformancesRegistered.performances.t'
}
check performanceCanBeCancelled for 10

//R19 
assert twoPerformancesDontOverlap{
	all t: Time, p1: PerformancesRegistered.performances.t, p2: PerformancesRegistered.performances.t | p1 != p2 => !(p1.begin_time < p2.end_time and p2.begin_time < p1.end_time)
}
check twoPerformancesDontOverlap for 10

//R20
assert noPerformancesRegAtBeg{
	no PerformancesRegistered.performances.first
}
check noPerformancesRegAtBeg for 10

//R21
assert reservationHasIDClientNumSeatsPerformance{
	all t: Time, r: Reservation | r.client in CLIENT and r.num_reserved_seats.t in Int and r.performance in PERFORMANCE
}
check reservationHasIDClientNumSeatsPerformance for 10

//R22
assert reservationCanBeCancelled{
	all t: Time, r:  ReservationsRegistered.reservations.t | let t' = t.next | cancelReservation[r, t, t']  => r not in ReservationsRegistered.reservations.t'
}
check reservationCanBeCancelled for 10

//R23
assert cancelReservationChangeAvailableSeats{
	all t: Time, r:  ReservationsRegistered.reservations.t | let t' = t.next | cancelReservation[r, t, t']  =>  r.performance.available_seats.t' = add[r.performance.available_seats.t, r.num_reserved_seats.t]
}
check cancelReservationChangeAvailableSeats for 10

//R24
assert clientWithReservationCantBeRemove{
	all t: Time,  r: ReservationsRegistered.reservations.t| let t' = t.next | removeClient[r.client, t, t'] => r.client in ClientsRegistered.clients.t'
}
check clientWithReservationCantBeRemove for 10

//R25
assert numReservationCannotExceedCapacity{ 
	all t: Time, r: ReservationsRegistered.reservations.t, n: Int | let t' = t.next | updateTheatre[r.performance.theatre, n, t, t']  => !makeReservation[r, t, t']
}
check numReservationCannotExceedCapacity for 10

//R26
assert clientBannedNotHaveReservations{
	all t: Time, r: ReservationsRegistered.reservations.t | let t' = t.next | banClient[r.client, t, t'] => r not in ReservationsRegistered.reservations.t' 
}
check clientBannedNotHaveReservations for 10

//R27
assert theatreCannotBeRemoveIfHavePerformance{
	all t: Time, p: PerformancesRegistered.performances.t | let t' = t.next | removeTheatre[p.theatre, t, t'] => p.theatre in TheatresRegistered.theatres.t' 
}
check theatreCannotBeRemoveIfHavePerformance for 10

//R28
assert registeredPerformanceHaveOnlyTheatreRegistered{
	all t: Time, p: PerformancesRegistered.performances.t |  p.theatre in TheatresRegistered.theatres.t 
}
check registeredPerformanceHaveOnlyTheatreRegistered for 10

//R29
assert registeredPerformanceHaveOnlyPlaysRegistered{
	all t: Time, p: PerformancesRegistered.performances.t |  p.play in PlaysRegistered.plays.t 
}
check registeredPerformanceHaveOnlyPlaysRegistered for 10

//R30
assert registeredReservationsHaveOnlyClientsRegistered{
	all t: Time, r: ReservationsRegistered.reservations.t |  r.client in ClientsRegistered.clients.t 
}
check registeredReservationsHaveOnlyClientsRegistered for 10
 
//R31
assert registeredReservationsHaveOnlyPerformancesRegistered{
	all t: Time, r: ReservationsRegistered.reservations.t |  r.performance in PerformancesRegistered.performances.t 
}
check registeredReservationsHaveOnlyPerformancesRegistered for 10



