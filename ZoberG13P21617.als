open util/ordering[Time]	

sig Time{} //Represents the states that will vary with time

//=================
//  Pre-defined Sets
//=================

sig CLIENTS {}
sig DRIVERS {}
sig CARS {}
sig NAMES {}
sig RIDES {}
sig EMAILS {}
sig LICENSES {}
enum ZOBERSERVICE {ZoberY, ZoberWhite }
enum PLAN {VIP, REGULAR} //R4
enum BAN {banned, notbanned}

//================
// Instances
//================

sig Client extends CLIENTS {  //R1
	
	name: one NAMES, //R2
	email: one EMAILS, //R2
	plan: PLAN one->Time, //R4
	rides: set Ride -> Time 

}

sig Driver extends DRIVERS { //R11
	name: one NAMES, //R12
	license: one LICENSES, //R12
	status: BAN one->Time,
	driverCars: Car set -> Time 
}

sig Car extends CARS{

	owner: one Driver,  //R19, R20
	drivers: set Driver ->Time,
	service: ZOBERSERVICE one->Time, //R24
	rides: set Ride -> Time   

}

sig Ride extends RIDES{ //R29   

	car: Car one -> Time,
	client: one Client,
	service: one ZOBERSERVICE,
	begin: one Int,
	end: one Int,
	grade:  Int one -> Time

}

//================
// Zober registered
//================	
 
one sig ClientsRegistered {clients: Client->Time}

one sig CarsRegistered {cars: Car->Time}

one sig DriversRegistered {drivers: Driver->Time}

one sig BookedRides {rides: Ride->Time}

//================
// Initialization
//================

pred init[t: Time] {

	no ClientsRegistered.clients.t //R5
	no CarsRegistered.cars.t //R25
	no DriversRegistered.drivers.t //R14
	no BookedRides.rides.t
	all c: Client | c.plan.t = REGULAR and no c.rides.t //R7
	all car: Car | car.service.t = ZoberY and no car.drivers.t and no car.rides.t //R26 
	all d: Driver | d.status.t = notbanned and no d.driverCars.t
	all r: Ride | no r.car.t and r.grade.t = 0

}

//=====================
// Unaltered states
//=====================

pred unalteredClientsRegistered [t, t': Time]{
	ClientsRegistered.clients.t' = ClientsRegistered.clients.t
}

pred unalteredCarsRegistered [t, t': Time]{
	CarsRegistered.cars.t' = CarsRegistered.cars.t
}

pred unalteredDriversRegistered [t, t': Time]{
	DriversRegistered.drivers.t' = DriversRegistered.drivers.t
}

pred unalteredBookedRides [t, t': Time]{
	BookedRides.rides.t' = BookedRides.rides.t
}

//================
// Operations - Clients
//================

pred newClient[c: Client, t, t': Time]{
	let cr = ClientsRegistered.clients{
		!(c in cr.t) //R6
		all clients : cr.t | c.email != clients.email //R3
		cr.t' = cr.t + c	
		c.plan.t' = REGULAR //R7

		//Not changed
		all cli : cr.t' | cli != c => cli.plan.t' = cli.plan.t
		all cli: cr.t' | cli.rides.t' = cli.rides.t 
	}
	unalteredCarsRegistered [t, t']
	unalteredDriversRegistered [t, t']
	unalteredBookedRides [t, t']
}

pred removeClient[c: Client, t, t': Time]{
	let cr = ClientsRegistered.clients{
		c in cr.t //R8
		cr.t' = cr.t - c
		#c.rides.t = 0 //R36

		//Not changed
		all cli : cr.t' | cli != c => cli.plan.t' = cli.plan.t 
		all cli: cr.t' | cli.rides.t' = cli.rides.t 
	}
	unalteredCarsRegistered [t, t']
	unalteredDriversRegistered [t, t']
	unalteredBookedRides [t, t']
}


pred upgradePlan[c: Client, t, t' : Time]{
	c.plan.t = REGULAR //R10
	let cr = ClientsRegistered.clients{
		c in cr.t //R9
		c.plan.t' = VIP

		//Not changed
		cr.t - c = cr.t' - c
		c in cr.t'
		all cli : cr.t' | cli != c => cli.plan.t' = cli.plan.t 
		all cli: cr.t' | cli.rides.t' = cli.rides.t 
	}
	unalteredCarsRegistered [t, t']
	unalteredDriversRegistered [t, t']
	unalteredBookedRides [t, t']
}

		
pred downgradePlan[c: Client, t, t' : Time]{
	c.plan.t = VIP //R10
	let cr = ClientsRegistered.clients{
		c in cr.t //R9
		c.plan.t' = REGULAR

		//Not changed
		cr.t - c = cr.t' - c
		c in cr.t'
		all cli : cr.t' | cli != c => cli.plan.t' = cli.plan.t 
		all cli: cr.t' | cli.rides.t' = cli.rides.t 
	}
	unalteredCarsRegistered [t, t']
	unalteredDriversRegistered [t, t']
	unalteredBookedRides [t, t']
}
	

//================
// Operations - Drivers
//================

pred newDriver[d: Driver, t, t': Time]{
	d.status.t = notbanned//R17
	let dr = DriversRegistered.drivers{
		!(d in dr.t) //R15
		all drivers : dr.t | drivers.license != d.license //R13
		dr.t' = dr.t + d	
		
		//Not changed
		all dri : dr.t' | dri != d => dri.status.t' = dri.status.t and dri.driverCars.t' = dri.driverCars.t
	}
	unalteredCarsRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredBookedRides [t, t']
}

pred removeDriver[d: Driver, t, t': Time]{	
	all c: Car | d in c.drivers.t => #c.drivers.t > 1 //R20 
	let dr = DriversRegistered.drivers{
		d in dr.t //R16
		dr.t' = dr.t - d	
		all c: d.driverCars.t | c.owner=d => #c.rides=0 //R40
		all c: Car | d in c.drivers.t => c.drivers.t' = c.drivers.t - d

		//Not changed
		all dri : dr.t' | dri != d => dri.status.t' = dri.status.t and dri.driverCars.t' = dri.driverCars.t
	}
	unalteredCarsRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredBookedRides [t, t']
}

pred banDriver[d: Driver, t, t' : Time]{ //R17
	d.status.t = notbanned
	let dr = DriversRegistered.drivers{
		d in dr.t
		d.status.t' = banned
		dr.t' = dr.t - d

		//R38     
		all car: d.driverCars.t | car.owner=d => BookedRides.rides.t' = BookedRides.rides.t - d.driverCars.t.rides.t
		all car: d.driverCars.t | car.owner=d => ClientsRegistered.clients.t.rides.t' = ClientsRegistered.clients.t.rides.t - d.driverCars.t.rides.t
		all car: d.driverCars.t | car.owner=d => CarsRegistered.cars.t' = CarsRegistered.cars.t' - car

		//Not changed
		all dri : dr.t'| dri != d => dri.status.t' = dri.status.t
		all dri: dr.t'| dri.driverCars.t' = dri.driverCars.t  
		all car: CarsRegistered.cars.t | car.owner != d => CarsRegistered.cars.t'= CarsRegistered.cars.t 
		all client: ClientsRegistered.clients.t | client.rides.t.car.t.owner != d => ClientsRegistered.clients.t' = ClientsRegistered.clients.t
		all ride: BookedRides.rides.t | ride.car.t.owner !=d => BookedRides.rides.t' = BookedRides.rides.t 
	}

}

//================
// Operations - Cars
//================
		
pred addCar[c: Car, t, t': Time]{
	c.owner in DriversRegistered.drivers.t
	#c.owner.driverCars.t <2 //R20
	//Car
	let cr = CarsRegistered.cars{
		!(c in cr.t) //R18
		cr.t' = cr.t + c	
		c.service.t' = ZoberY //R26
		c.drivers.t' = c.owner //R20, R21   
 
		//Driver
		c.owner.driverCars.t' = c.owner.driverCars.t + c

		//Not changed
		all cri : cr.t' | cri != c => cri.service.t' = cri.service.t and cri.drivers.t' = cri.drivers.t
		all cri: cr.t | cri.rides.t' = cri.rides.t
	}
	unalteredDriversRegistered [t, t']
	unalteredClientsRegistered [t, t']
	unalteredBookedRides [t, t']
}

pred removeCar[c: Car, t, t': Time]{	
	let cr = CarsRegistered.cars{
		c in cr.t //R27
		cr.t' = cr.t - c
		all d: Driver | d in c.drivers.t => d.driverCars.t' = d.driverCars.t - c
		#c.rides.t=0 //R39	
		
		//Not changed
		all cri : cr.t' | cri != c => cri.service.t' = cri.service.t and cri.drivers.t' = cri.drivers.t
		all d:Driver | d not in c.drivers.t  => d.driverCars.t' = d.driverCars.t 
		all d:Driver | d.status.t'=d.status.t
		all cri: cr.t | cri.rides.t' = cri.rides.t
		
	}

	unalteredClientsRegistered [t, t']
	unalteredBookedRides [t, t']
}

pred addDriverToCar[c: Car, d: Driver, t, t': Time]{
	d in DriversRegistered.drivers.t //R22, R28
	c in CarsRegistered.cars.t
	#d.driverCars.t < 2 //R23
	#c.drivers.t < 3 //R20
	c not in d.driverCars.t
	d not in c.drivers.t

	d.driverCars.t' = d.driverCars.t + c
	c.drivers.t' = c.drivers.t + d

	//Not changed
	all cri : CarsRegistered.cars.t' | cri != c => cri.service.t' = cri.service.t and cri.drivers.t' = cri.drivers.t
	all dri : DriversRegistered.drivers.t' | dri != d => dri.status.t' = dri.status.t and dri.driverCars.t' = dri.driverCars.t
	all cri: CarsRegistered.cars.t | cri.rides.t' = cri.rides.t

	unalteredClientsRegistered [t, t']
	unalteredBookedRides [t, t']
}	
	
pred removeDriverFromCar[c: Car, d: Driver, t, t': Time]{
	d in DriversRegistered.drivers.t //R28
	c in CarsRegistered.cars.t
	#c.drivers.t > 1 //R20
	c.owner != d //R20
	c in d.driverCars.t
	d in c.drivers.t

	d.driverCars.t' = d.driverCars.t - c
	c.drivers.t' = c.drivers.t - d

	//Not changed
	all cri : CarsRegistered.cars.t' | cri != c => cri.service.t' = cri.service.t and cri.drivers.t' = cri.drivers.t
	all cri: CarsRegistered.cars.t | cri.rides.t' = cri.rides.t
	all dri : DriversRegistered.drivers.t' | dri != d => dri.status.t' = dri.status.t and dri.driverCars.t' = dri.driverCars.t

	unalteredClientsRegistered [t, t']
	unalteredBookedRides [t, t']
}

pred upgradeService[c: Car, t, t': Time]{
	c.service.t=ZoberY	
	let cr = CarsRegistered.cars{ 
		c in cr.t
		c.service.t'=ZoberWhite
		
		//Not changed
		cr.t - c = cr.t' - c
		c in cr.t'
		all cars : cr.t' | cars != c => cars.service.t' = cars.service.t  and cars.drivers.t' = cars.drivers.t
	}
	unalteredClientsRegistered [t, t']
	unalteredDriversRegistered [t, t']
	unalteredBookedRides [t, t']
}


pred downgradeService[c: Car, t, t' : Time]{
	c.service.t = ZoberWhite 
	let cr = CarsRegistered.cars{
		c in cr.t
		c.service.t' = ZoberY

		//Not changed
		cr.t - c = cr.t' - c
		c in cr.t'
		all cars : cr.t' | cars != c => cars.service.t' = cars.service.t and cars.drivers.t' = cars.drivers.t
	}
	unalteredClientsRegistered [t, t']
	unalteredDriversRegistered [t, t']
	unalteredBookedRides [t, t']
}

//================
// Operations - Rides
//================

pred newRide[r: Ride, t, t' : Time]{

	let br= BookedRides.rides{
		!(r in br.t)

		 some c: CarsRegistered.cars.t | all ride : c.rides.t |c.service.t = r.service  and (r.end< ride.begin or r.begin > ride.end) => r.car.t'= c  // R30, R29, R32

		r.end >r.begin // R31
		
		r.client.plan.t = VIP => r.car.t.service.t = ZoberWhite //R35

		r.client.plan.t = REGULAR => #r.client.rides <2 //R34
		r.client.rides.t'= r.client.rides.t + r

		r.car.t.rides.t' = r.car.t.rides.t + r
		
		r.grade.t' = 0 

		br.t' = br.t + r

		//Not Changed
		all rides : br.t' | rides != r => rides.grade.t' = rides.grade.t
		all cars : CarsRegistered.cars.t' | cars != r.car.t => cars.rides.t' = cars.rides.t
		all cars : CarsRegistered.cars.t' | cars.service.t' = cars.service.t and cars.drivers.t' = cars.drivers.t
		all clients : ClientsRegistered.clients.t' | clients != r.client => clients.rides.t' = clients.rides.t
		all clients : ClientsRegistered.clients.t' | clients.plan.t' = clients.plan.t 				
	}
	unalteredDriversRegistered [t, t']
}

pred cancelRide[r: Ride, t, t' : Time]{

	let br= BookedRides.rides{
		(r in br.t)
		r.client.rides.t'=r.client.rides.t - r
		r.car.t.rides.t'=r.car.t.rides.t - r
		br.t'=br.t - r
		r.grade.t=0 //R37

		//Not Changed
		br.t'-r = br.t -r
		all cars : CarsRegistered.cars.t' | cars != r.car.t => cars.rides.t' = cars.rides.t
		all cars : CarsRegistered.cars.t' | cars.service.t' = cars.service.t and cars.drivers.t' = cars.drivers.t
		all clients : ClientsRegistered.clients.t' | clients != r.client => clients.rides.t' = clients.rides.t
		all clients : ClientsRegistered.clients.t' | clients.plan.t' = clients.plan.t 
	}
	unalteredDriversRegistered [t, t']
}		

pred completeRide[r: Ride, g: Int, t, t': Time]{
	let br= BookedRides.rides{
		(r in br.t)
		1 <= g // R33
		g <= 5 //R33
		r.grade.t' = g
		r.client.rides.t'=r.client.rides.t - r
		r.car.t.rides.t'=r.car.t.rides.t - r
		br.t'=br.t - r	
 
		//Not Changed
		all rides : br.t' | rides != r => rides.grade.t' = rides.grade.t
		all cars : CarsRegistered.cars.t' | cars != r.car.t => cars.rides.t' = cars.rides.t
		all cars : CarsRegistered.cars.t' | cars.service.t' = cars.service.t and cars.drivers.t' = cars.drivers.t
		all clients : ClientsRegistered.clients.t' | clients != r.client => clients.rides.t' = clients.rides.t
		all clients : ClientsRegistered.clients.t' | clients.plan.t' = clients.plan.t 
	}
	unalteredDriversRegistered [t, t']
}		


//================
// Begin
//================

fact traces {
	init[first]
	all t: Time-last | let t'=t.next |
		some c: Client, d: Driver, ca: Car, r: Ride, g: Int | 
			newClient[c, t, t'] or
			removeClient[c, t, t'] or
			newDriver[d, t, t']or
			removeDriver[d, t, t']or
			addCar[ca, t,t'] or
			removeCar[ca, t, t'] or
			addDriverToCar[ca, d, t, t'] or
			removeDriverFromCar[ca, d, t, t'] or 
			upgradePlan[c, t, t'] or
			downgradePlan[c, t, t'] or
			banDriver[d, t, t'] or
			upgradeService[ca, t, t'] or
			downgradeService[ca, t, t'] or
			newRide[r, t, t'] or
			cancelRide[r, t, t'] or
			completeRide[r, g, t, t']
}



//================
// Asserts
//================

//R1
assert everyClientMayRegister{
	all t:Time, c:Client | let t' = t.next | newClient[c, t, t'] => c in ClientsRegistered.clients.t'
}
check everyClientMayRegister for 10

//R2
assert everyClientHasNameAndEmail{
	all c:ClientsRegistered.clients.Time | c.name in NAMES and c.email in EMAILS
}
check everyClientHasNameAndEmail for 10

//R3
assert everyEmailInZoberIsUnique{   
	all t:Time, c1, c2 : CLIENTS, e: EMAILS | let t' = t.next | c1 != c2 and c1 in ClientsRegistered.clients.t and c1.email=e and newClient[c2,t,t'] => c2.email != e  
}
check everyEmailInZoberIsUnique for 10

//R4
assert planRegularOrVip{
	all t:Time, c: ClientsRegistered.clients.t | c.plan.t in PLAN 
}
check planRegularOrVip for 10

//R5
assert noClientsRegAtBeg{
	no ClientsRegistered.clients.first
}
check noClientsRegAtBeg for 10

//R6
assert newClientNotRegBefore {     
	all t: Time, c:Client , cr: ClientsRegistered.clients | let t'=t.next |
		newClient[c, t, t'] => c not in cr.t	                                                  
}   
check newClientNotRegBefore for 10

//R7
assert newClientPlanIsRegular{
	all t: Time, c:Client, cr: ClientsRegistered.clients | let t' = t.next | 
		c not in cr.t => c.plan.t = REGULAR and
		newClient[c, t, t'] =>  c.plan.t' = REGULAR
}
check newClientPlanIsRegular for 10

//R8
assert removeOnlyRegClient {    
	all t: Time, c:Client | let t' = t.next |  
	removeClient[c, t, t'] => c in ClientsRegistered.clients.t 		
}
check removeOnlyRegClient for 10

//R9
assert upgradeOrDowngradeOnlyRegClient{
	all t: Time, c:Client, cr: ClientsRegistered.clients | let t' = t.next | 
		upgradePlan[c, t, t']  => c in cr.t   and	
		downgradePlan[c,t,t'] => c in cr.t               
}
check upgradeOrDowngradeOnlyRegClient for 10

//R10
assert onlyRegularMayBeUpgraded{
	all t: Time, c:Client | let t' = t.next |
		upgradePlan[c,t,t'] => c.plan.t = REGULAR
}
check onlyRegularMayBeUpgraded  for 10

//R11
assert everyDriverMayRegister{
	all t:Time, d:Driver | let t' = t.next | newDriver[d, t, t'] => d in DriversRegistered.drivers.t'
}
check everyDriverMayRegister for 10

//R12
assert everyDriverHasNameAndLicense{
	all dr:DriversRegistered.drivers.Time | dr.name in NAMES and dr.license in LICENSES
}
check everyDriverHasNameAndLicense for 10

//R13
assert everyLicenseInZoberIsUnique{  
	all t:Time, d1, d2 : DRIVERS, l: LICENSES | let t' = t.next | 
		d1 != d2 and d1 in DriversRegistered.drivers.t and d1.license=l  and newDriver[d2,t,t'] => d2.license != l  
}
check everyLicenseInZoberIsUnique for 10

//R14
assert noDriversRegAtBeg{
	no DriversRegistered.drivers.first
}
check noDriversRegAtBeg for 10

//R15
assert newDriverNotRegBefore {
	all t: Time, d:Driver , dr: DriversRegistered.drivers | let t'=t.next |
	newDriver[d, t, t'] => d not in dr.t                                                        
}
check newDriverNotRegBefore for 10

//R16
assert removeOnlyRegDriver {  
	all t: Time, d:Driver| let t' = t.next | 
		removeDriver[d,t, t'] => d in DriversRegistered.drivers.t
}
check removeOnlyRegDriver for 10

//R17
assert cannotAddBannedDriver{	
	all t: Time, d, d1:Driver | let t' = t.next |
		banDriver[d, t, t'] => !newDriver[d, t, t'] and
		banDriver[d, t, t'] and newDriver[d1, t, t'] => d != d1      
}
check cannotAddBannedDriver

//R18
assert everyCarMayBeRegistered{
	all t:Time, c:Car | let t' = t.next | (c in CarsRegistered.cars.t) or  (addCar[c, t, t'] => c in CarsRegistered.cars.t')
}
check everyCarMayBeRegistered for 10

//R19
assert regCarsHaveSingleOwner{
	all t:Time, c: CarsRegistered.cars.t | #c.owner=1
}
check regCarsHaveSingleOwner for 10

//R20
assert regCarsHave1to3Drivers{  
	all t:Time, d: DriversRegistered.drivers.t, c1: CarsRegistered.cars.t, c2:CARS | let t' = t.next |  
		addCar[c2, t, t'] => (#c2.drivers.t' >= 1 and #c2.drivers.t' <=3) and
		addDriverToCar[c1, d, t, t'] => (#c1.drivers.t >= 1 and #c1.drivers.t <=2) and
		removeDriverFromCar[c1, d, t, t'] => (#c1.drivers.t > 1 and #c1.drivers.t <=3)
}
check regCarsHave1to3Drivers for 10

//R21
assert ownerOfCarIsDriverOfCar{ 		
	all t:Time, c1: CarsRegistered.cars.t, c2:CARS, d: DriversRegistered.drivers.t| let t' = t.next |  
		addCar[c2, t, t'] => c2.owner in c2.drivers.t' and
		removeDriverFromCar[c1, d, t, t'] => c1.owner in c1.drivers.t'
}
check ownerOfCarIsDriverOfCar for 10
 
//R22
assert onlyRegDriversMayBeCarDrivers{ 	
	all t:Time, c1: CarsRegistered.cars.t, c2:CARS, d:DRIVERS| let t' = t.next |
		addDriverToCar[c1, d, t, t'] => d in DriversRegistered.drivers.t and
		addCar[c2, t, t'] => c2.owner in DriversRegistered.drivers.t
}
check onlyRegDriversMayBeCarDrivers for 10

//R23
assert driverCarsLessThan3{           
	all t:Time, d: DriversRegistered.drivers.t, c1: CarsRegistered.cars.t, c2:CARS | let t' = t.next |  
		addCar[c2, t, t'] => #c2.owner.driverCars.t<2 and
		addDriverToCar[c1, d, t, t'] => #d.driverCars.t <2	
}
check driverCarsLessThan3 for 10

//R24
assert serviceYOrWhite{
	all t:Time, c: CarsRegistered.cars.t | c.service.t in ZOBERSERVICE
}
check serviceYOrWhite for 10

//R25
assert noCarsRegAtBeg{
	no CarsRegistered.cars.first
}
check noCarsRegAtBeg for 10

//R26
assert initiServiceZoberY{
	all t: Time, c:Car, cr: CarsRegistered.cars | let t' = t.next |
		c not in cr.t => c.service.t = ZoberY and
		addCar[c, t, t'] => c.service.t'=ZoberY
}
check initiServiceZoberY for 10

//R27
assert removeOnlyRegCars{   
	all t: Time, c:Car | let t' = t.next |  
		removeCar[c, t, t'] => c in CarsRegistered.cars.t
}
check removeOnlyRegCars for 10

//R28
assert addOrRemoveOnlyRegDriversFromCar{
	all t: Time, c: Car, d:Driver, dr:DriversRegistered.drivers | let t' = t.next |
		addDriverToCar[c, d, t, t'] => d in dr.t and
		removeDriverFromCar[c, d, t, t'] => d in dr.t
}
check addOrRemoveOnlyRegDriversFromCar for 10

//R29   
assert rideHasIdClientTimeServiceCar{
	all t:Time, r : BookedRides.rides.Time | r.client in CLIENTS and r.begin in Int and r.end in Int and r.service in ZOBERSERVICE and
		r.car.t in CARS and r.grade.t in Int
}	
check rideHasIdClientTimeServiceCar for 10

//R30
assert rideCarService{        
	all r: RIDES, t:Time |let t' = t.next |
		newRide[r, t, t'] =>  r.car.t.service.t = r.service 
}
check rideCarService for 10

//R31
assert rideWellFormed{        	
	all t:Time, r: RIDES| let t' = t.next | 
		newRide[r,t,t'] => r in BookedRides.rides.t' and r.end > r.begin
}
check rideWellFormed for 10

//R32
assert noOverlappingRides{  
	all t:Time, r1: RIDES , r2:BookedRides.rides.t | let t' = t.next | 
		newRide[r1, t, t'] => 
					((r1.end < r2.begin or r1.begin > r2.begin) => r1.car = r2.car) or 
					 (r1.car != r2.car)
}
check noOverlappingRides for 10

//R33
assert completeRideRate{
	all t:Time, r : BookedRides.rides.Time | let t' = t.next | some g : Int |
		r.grade.t = 0 and 
		completeRide[r, g, t, t'] => r.grade.t' >= 1 and r.grade.t' <= 5 and r not in BookedRides.rides.t' 
}
check completeRideRate for 10

//R34
assert nrRidesVIPorREGULAR{
	all t:Time, c: ClientsRegistered.clients.Time |
 	c.plan.t = REGULAR => #c.rides.t < 3 and
	c.plan.t = VIP => #c.rides in Int
}
check nrRidesVIPorREGULAR for 10

//R35
assert VIPClientsOnlyUseZoberWhite{     
	all  c : ClientsRegistered.clients.Time, ride: RIDES|		
		 c.plan.Time = VIP and ride in c.rides.Time => ride.service = ZoberWhite
}
check VIPClientsOnlyUseZoberWhite for 10

//R36
assert clientsWithRidesCannotBeRemoved{
	all t:Time, c: ClientsRegistered.clients.Time |let t' = t.next |
	removeClient[c, t, t'] => #c.rides.t = 0
}
check clientsWithRidesCannotBeRemoved for 10

//R37
assert nonCompleteRideCanBeCanceled{
	all t: Time, r: BookedRides.rides.Time | let t' = t.next |
	cancelRide[r, t, t'] => r.grade.t =0
}
check nonCompleteRideCanBeCanceled for 10

//R38
assert banDriverAndRemoveCarsAndRides{   
	all t: Time, d: DriversRegistered.drivers.Time, cd: CarsRegistered.cars.t| let t' = t.next |	
		banDriver[d, t, t'] => 
				(cd.rides.t not in BookedRides.rides.t' and
				 cd.rides.t not in ClientsRegistered.clients.t.rides.t' and
			          cd not in CarsRegistered.cars.t'   => cd.owner=d)

}
check  banDriverAndRemoveCarsAndRides for 10

//R39
assert carCannotBeRemovedWithReservations{   
	all t:Time, c: CarsRegistered.cars.Time |let t' = t.next |
	removeCar[c, t, t'] => #c.rides.t = 0 
}
check carCannotBeRemovedWithReservations for 10

//R40
assert ownerCannotBeRemovedWithReservationsForHisCars{
	all t:Time, d: DriversRegistered.drivers.t|let t' = t.next |
	removeDriver[d, t, t'] => (#driverCars.rides !=0 => d.driverCars.t.owner != d) 
}
check ownerCannotBeRemovedWithReservationsForHisCars for 10
