import math
import json
from pkgutil import get_data
import mysql.connector as mysql
import random
from mysqlx import IntegrityError
import names
import string
import datetime
import threading
from barnum import gen_data
from numpy import insert, tri
from datetime import date, timedelta


class Empty(Exception):
    pass

class Exclude(Exception):
    pass

class Disjoint_set:
    def __init__(self,n) -> None:
        self.set=[-1]*n
    def find_root(self,i):
        while self.set[i]>=0:
            i=self.set[i]
        return i
    def union(self, i, j):
        parent_i = self.find_root(i)
        parent_j = self.find_root(j)
        if parent_i == parent_j:
            return
        if self.set[parent_i] <= self.set[parent_j]:
            self.set[parent_i] = self.set[parent_i] + self.set[parent_j]
            self.set[parent_j] = parent_i
        else:
            self.set[parent_j] = self.set[parent_j] + self.set[parent_i]
            self.set[parent_i] = parent_j


##graph class based on adjacency

##edge class

class Edge:

    def __init__(self, u, v, data=None) -> None:
        self._origin = u
        self._destination = v
        self._data = data

    def endpoints(self):
        return (self._origin, self._destination)

    def opposite(self, v):
        if v != self._origin and v != self._destination:
            raise Exclude('the vertex is not in the endpoins!')
        return self._destination if v is self._origin else self._origin

    def data(self):
        return self._data

    def __hash__(self) -> int:
        return hash((self._origin, self._destination))

class Queue:
    DEFAULT_CAPACITY =10
    def __init__(self) -> None:
        self._data =[None ] *Queue.DEFAULT_CAPACITY
        self._size =0
        self._first =0
    def __len__(self) -> int:
        return self._size
    def is_empty(self) -> bool:
        return self._size ==0
    def front(self):
        if self.is_empty():
            raise Empty('queue is empty! cannot retrieve data.')
        return self._data[self._first]
    def dequeue(self):
        if self.is_empty():
            raise Empty('queue is empty! cannot remove data.')
        deleted_data =self._data[self._first]
        self._data[self._first ] =None
        self._first =(self._first +1 ) %len(self._data)
        self._size -=1
        return deleted_data
    def enqueue(self ,data):
        if self._size == len(self._data):
            self._resize( 2 *self._size)
        index = (self._first +self._size ) %len(self._data)
        self._data[index] =data
        self._size +=1
    def _resize(self ,size):
        temp =[None ] *size
        j=self._first
        for i in range(self._size):
            temp[i]=self._data[j]
            j=(j+1)%len( self._data)
        self._data=temp
        self._first=0

##vertex class


class Vertex:
    def __init__(self, data=None) -> None:
        self._data = data

    def data(self):
        return self._data

    def __hash__(self) -> int:
        return hash(id(self))


##graph class 

class Graph:
    def __init__(self, directed=False) -> None:
        self._outgoing = {}
        self._incoming = {} if directed else self._outgoing

    def is_direccted(self):
        return self._incoming is not self._outgoing

    def vertex_count(self):
        return len(self._outgoing)

    def vertices(self):
        return list(self._outgoing.keys())

    def all_edge_count(self):
        total = sum(len(self._outgoing[v] for v in self._outgoing))
        return total if self.is_direccted() else total // 2

    def check_edge(self,v1,v2):
        return self._outgoing[v1].get(v2)
    def edges(self):
        result = set()
        for edge_set in self._outgoing.values():
            result.update(edge_set.values())
        return result

    def get_edge(self, u, v):
        return self._outgoing[u].get(v)

    def degree(self, v, outgoing=True):
        adj = self._outgoing if outgoing else self._incoming
        return len(adj)

    def vertex_edge(self, v, outgoing=True):
        adj = self._outgoing if outgoing else self._incoming
        return list(adj[v].values())

    def vertex_neighbours(self, v):
        return self._outgoing[v].keys()

    def insert_vertex(self,data):
        v = Vertex(data)
        self._outgoing[v] = {}
        if self.is_direccted():
            self._incoming[v] = {}
        return v

    def insert_edge(self, u, v, data):
        e = Edge(u, v,data)
        self._outgoing[u][v] = e
        self._incoming[v][u] = e

    def get_vertex_by_data(self,data):
        for v in self._outgoing.keys():
            if v.data()==data:
                return v
        return None

CONFIG = {
    'user' : '',
    'password' : '',
    'host' : 'localhost',
    'database' : 'Train'
}

def get_cities():
    f=open('city.json')
    data=json.load(f)
    return list(set([a['city'] for a in data]))

def random_date(year1,year2,month1,month2,day1,day2,hour1,hour2,min1,min2,sec1,sec2):
    return datetime.datetime(random.randint(year1,year2),random.randint(month1,month2)
                             ,random.randint(day1,day2),random.randint(hour1,hour2),
                             random.randint(min1,min2),random.randint(sec1,sec2))

CELL_PHONE_NUMBER_PREFIX=[
    '0912','0916','0921','0936','0944','0911','0965','0988','0917','0915'                     
]

PHONE_NUMBER_PREFIX=[
    '051','022','033','061','032','021','010','044','036','050'
]

def random_phone_number():
    index=random.randrange(len(PHONE_NUMBER_PREFIX))
    return PHONE_NUMBER_PREFIX[index]+''.join(random.choices(string.digits,k=7))


def random_cell_phone_number():
    index=random.randrange(len(CELL_PHONE_NUMBER_PREFIX))
    return CELL_PHONE_NUMBER_PREFIX[index]+''.join(random.choices(string.digits,k=7))

def add_random_date(start,end,l):
   current = start
   diff=(end-start).seconds
   times=[]
   while l >= 0:
      add=random.randint(diff//10,diff//2)
      diff-=add
      curr = current + timedelta(seconds=add)
      times.append(str(curr))
      current=curr
      l-=1
   return times

def bfs(g,v) -> list:
    visited={v:None}
    wait_list=Queue()
    wait_list.enqueue(v)
    while not wait_list.is_empty():
        u=wait_list.front()
        for k in g.vertex_neighbours(u):
            if k not in visited:
                visited[k]=g.get_edge(u,k)
                wait_list.enqueue(k)
        wait_list.dequeue()
    return visited

def create_path_graph(visited,u,v):
    if visited.get(v)==None:
        return None
    path=[v]
    p=v
    while p is not u:
        e=visited[p]
        p=e.opposite(p)
        path.append(p)
    path.reverse()
    return path

def multi_insert_traveller(query,data):
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    cursor.executemany(query,data)
    cnx.commit()
    cnx.close()

def multi_insert_train_track(query,data):
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    cursor.executemany(query,data)
    cnx.commit()
    cnx.close()
    
def multi_insert_train_seat(query,trains):
        cnx=mysql.connect(**CONFIG)
        cursor=cnx.cursor()
        data=[]
        for t in trains:
            id=t[0]
            number_of_carriages=t[1]
            seat=t[2]//t[1]
            for i in range(1,number_of_carriages+1):
                for j in range(1,seat+1):
                    data.append((i,j,random.choice('ABCD'),id))
        cursor.executemany(query,data)   
        cnx.commit()
        cnx.close()
        

def insert_traveller(n,m):
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    query_traveller='''INSERT INTO Traveller(national_code,first_name,last_name,phone_number,
    date_of_birth,gender)
    VALUES(%s,%s,%s,%s,%s,%s)
    '''
    national_code=random.sample(range(int(10e8),int(10e9)),k=n)
    data=[]
    for i in range(n):
            code=national_code[i]
            gender=i%2
            first_name=names.get_first_name(gender=('male' if gender else 'female'))
            last_name=names.get_last_name()  
            phone_number=random_cell_phone_number()
            date_of_birth=random_date(1920,2020,1,12,1,28,0,23,0,59,0,59)
            data.append((code,first_name,last_name,phone_number,date_of_birth,gender))
    q=math.ceil(len(data)/m)
    t=[]
    for i in range(m):
        t.append(threading.Thread(target=multi_insert_traveller,args=(query_traveller,data[i*q:q*(i+1)])))
    for i in range(m):
        t[i].start()
    for i in range(m):
        t[i].join()



def insert_station(n):
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    query_sation='''INSERT INTO Station(name,establishment_date,city)
    VALUES(%s,%s,%s)
    '''
    query_station_phone_number='''INSERT INTO Station_phone_number(phone_number,station_id)
    VALUES('{phone_number}','{station_id}')
    '''
    cities=random.sample(get_cities(),k=n)
    data=[]
    for i in range(n):
        data.append((gen_data.create_nouns(1),random_date(1940,2015,1,12,1,28,0,23,0,59,0,59),cities[i]))
    cursor.executemany(query_sation,data)
    cursor.execute('SELECT id FROM Station')
    station_id=[res[0] for res in cursor.fetchall()]
    for i in range(len(station_id)):
        for j in range(2,5):
            while True:
                try:
                    cursor.execute(query_station_phone_number.format(
                        phone_number=random_phone_number(),
                        station_id=station_id[i]    
                    ))
                    break
                except mysql.IntegrityError as err:
                    continue
    cnx.commit()
    cnx.close()



def insert_company(n):
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    query_company='''INSERT INTO Company(name,foundation_date,city)
    VALUES(%s,%s,%s)
    '''
    query_company_phone_number='''INSERT INTO Company_phone_number(phone_number,company_id)
    VALUES('{phone_number}','{company_id}')
    '''
    query_train='''INSERT INTO Train(model,number_of_carriages,capacity,owner_company_id)
    VALUES('{model}',{number_of_carriages},{capacity},{owner_company_id})
    '''
    data=[]
    for i in range(n):
        data.append((gen_data.create_company_name(1),random_date(1940,2015,1,12,1,28,0,23,0,59,0,59),random.choice(get_cities())))
    cursor.executemany(query_company,data)
    cursor.execute('SELECT id FROM Company')
    company_id=[res[0] for res in cursor.fetchall()]
    for i in range(len(company_id)):
        for j in range(random.randint(1,5)):
            while True:
                try:
                    cursor.execute(query_company_phone_number.format(
                        phone_number=random_phone_number(),
                        company_id=company_id[i]    
                    ))
                    break
                except mysql.IntegrityError as err:
                    continue
    for i in range(len(company_id)):
        owner_company_id=company_id[i]
        for j in range(random.randint(4,10)):
            model=''.join(random.choices(string.ascii_uppercase+string.digits))
            number_of_carriages=random.randint(4,10)
            room_capacity=random.choice([30,40,50,60])
            capacity=number_of_carriages*room_capacity
            cursor.execute(query_train.format(
                model=model,
                number_of_carriages=number_of_carriages,
                capacity=capacity,
                owner_company_id=owner_company_id
            ))
    cnx.commit()
    cnx.close()     


def insert_train_seat(m):
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    query_train_selecet='''SELECT id,number_of_carriages,capacity FROM Train
    '''
    query_train_seat='''INSERT INTO Train_seat(carriage_number,seat_number,class,train_id)
    VALUES(%s,%s,%s,%s)
    ''' 
    cursor.execute(query_train_selecet)
    trains=cursor.fetchall()
    q=math.ceil(len(trains)/m)
    t=[]
    for i in range(m):
        t.append(threading.Thread(target=multi_insert_train_seat,args=(query_train_seat,trains[i*q:q*(i+1)])))
    for i in range(m):
        t[i].start()
    for i in range(m):
        t[i].join()
      
def insert_train_tracks(n,m):
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    query_station_id='SELECT id FROM Station'
    query_train_track='''INSERT INTO Train_track(from_station_id,to_station_id,distance)
    VALUES(%s,%s,%s)
    '''
    cursor.execute(query_station_id)
    station_id=[res[0] for res in cursor.fetchall()]
    data=[]
    edges={}
    for i in range(n):
        while True:
            j,k=random.sample(range(len(station_id)),2)
            v=station_id[j]
            u=station_id[k]
            if edges.get((v,u))==None:   
                edges[(v,u)]=True
                data.append((v,u,random.randint(50,500)))
                break
    q=math.ceil(len(data)/m)
    t=[]
    for i in range(m):
        t.append(threading.Thread(target=multi_insert_train_track,args=(query_train_track,data[i*q:q*(i+1)])))
    for i in range(m):
        t[i].start()
    for i in range(m):
        t[i].join()
 
def create_graph():
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    g=Graph(directed=True)
    query_station_id='SELECT id FROM Station'
    query_track_id='''SELECT id,from_station_id,to_station_id FROM Train_track
    '''
    cursor.execute(query_station_id)
    stations=[res[0] for res in cursor.fetchall()]
    cursor.execute(query_track_id)
    edges=list(cursor.fetchall())
    for station in stations:
        g.insert_vertex(station)
    for e in edges:
        v=g.get_vertex_by_data(e[1])
        u=g.get_vertex_by_data(e[2])
        w=e[0]
        g.insert_edge(v,u,w)
    cnx.close()
    return g    

def insert_trip(n):
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    query_trip='''INSERT INTO Trip(rate,departure_time,arrival_time,from_station_id,to_station_id,train_id,company_id)
    VALUES({rate},'{departure_time}','{arrival_time}',{from_station_id},{to_station_id},{train_id},{company_id})
    '''
    query_get_train='''SELECT Company.id ,Train.ID  FROM Company
    INNER JOIN Train ON Train.owner_company_id=Company.id
    '''
    query_select_seat='''SELECT Train_seat.id FROM Train
    INNER JOIN Train_seat ON Train.id=Train_seat.train_id 
    WHERE Train.id={train_id}
    '''
    query_ticket='''INSERT INTO Ticket(price,train_seat_id,trip_id)
    VALUES(%s,%s,%s)
    '''
    cursor.execute(query_get_train)
    trains=cursor.fetchall()
    map=create_graph()
    for i in range(n):
        while True: 
            try:
                company_id,train_id=random.choice(trains)
                rate=random.randint(3,10)
                v,u=random.sample(map.vertices(),k=2)
                from_station_id,to_station_id=v.data(),u.data()
                departure_time=random_date(2010,2020,1,12,1,28,0,23,0,59,0,59)
                arrival_time=departure_time+datetime.timedelta(minutes=random.randrange(60,24*60))
                cursor.execute(query_trip.format(
                    rate=rate,
                    departure_time=departure_time,
                    arrival_time=arrival_time,
                    from_station_id=from_station_id,
                    to_station_id=to_station_id,
                    train_id=train_id,
                    company_id=company_id
                ))      
                trip_id=cursor.lastrowid
                cursor.execute(query_select_seat.format(train_id=train_id))
                seats=[res[0] for res in cursor.fetchall()]
                data=[]
                for seat in seats:
                    data.append((random.randint(100,500),seat,trip_id))
                cursor.executemany(query_ticket,data)
                break
            except mysql.IntegrityError as err:
                    continue
    cnx.commit()
    cnx.close()
             
def insert_train_stops():
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    query_trip_stop='''INSERT INTO Trip_stops(departure_time,arrival_time,train_track_id,trip_id)
    VALUES('{departure_time}','{arrival_time}',{train_track_id},{trip_id})
    ''' 
    query_trip_select='''SELECT id,from_station_id,to_station_id,departure_time,arrival_time
    FROM Trip
    '''
    query_delete_trip='''DELETE FROM Trip WHERE id=%s
    '''
    query_delete_ticket='''DELETE FROM Ticket WHERE trip_id=%s
    '''
    cursor.execute(query_trip_select)
    trips=cursor.fetchall()
    g=create_graph()
    rejected_trip=[]
    j=0
    for trip in trips:
        try:
            v=g.get_vertex_by_data(trip[1])
            u=g.get_vertex_by_data(trip[2])
            path=create_path_graph(bfs(g,v),v,u)
            if path==None:
                rejected_trip.append((trip[0],))
                continue
            times=add_random_date(trip[3],trip[4],len(path))
            times[0]=trip[3]
            times[len(path)-1]=trip[4]
            for i in range(len(path)-1):
                cursor.execute(query_trip_stop.format(
                    departure_time=times[i],
                    arrival_time=times[i+1],
                    train_track_id=g.get_edge(path[i],path[i+1]).data(),
                    trip_id=trip[0]
                ))
        except mysql.IntegrityError as err:
            rejected_trip.append((trip[0],))
            continue
    cursor.executemany(query_delete_trip,rejected_trip)
    cursor.executemany(query_delete_ticket,rejected_trip)
    cnx.commit()    
    cnx.close()
  
def buy_ticket():
    query_ticket='''INSERT INTO Ticket(price,purchase_date,trip_id,train_seat_id,traveller_id)
    VALUES(%s,%s,%s,%s,%s)
    '''
    query_get_trips='''SELECT id,departure_time FROM Trip
    
    '''
    query_get_traveller='''SELECT id FROM Traveller
    '''
    querry_get_seat_id='''SELECT Train_seat.id FROM Trip
    INNER JOIN Train ON Trip.train_id=Train.id
    INNER JOIN Train_seat ON Train_seat.train_id=Train.id
    WHERE Trip.id={trip_id}
    '''
    cnx=mysql.connect(**CONFIG)
    cursor=cnx.cursor()
    cursor.execute(query_get_trips)
    trips=cursor.fetchall()
    cursor=cnx.cursor()
    cursor.execute(query_get_traveller)
    travellers=cursor.fetchall()
    tickets=[]
    for trip in trips:
        dep_time=trip[1]
        buy_time=dep_time-datetime.timedelta(minutes=7*24*60*60)
        diff=(dep_time-buy_time).seconds
        cursor.execute(querry_get_seat_id.format(trip_id=trip[0]))  
        train_seats=cursor.fetchall()
        for t in train_seats:
            
            last_time= buy_time+datetime.timedelta(seconds=random.randint(0,diff))
            traveller_id=random.choice(travellers)
            price=random.randint(200,600)
            if random.random()<0.72:
                tickets.append((price,last_time,trip[0],t[0],traveller_id[0]))
            else:
                tickets.append((price,buy_time,trip[0],t[0],None))
    cursor.executemany(query_ticket,tickets)
    cnx.commit()    
    cnx.close()
    
if __name__=='__main__':
    buy_ticket()
