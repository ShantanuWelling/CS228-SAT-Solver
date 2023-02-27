### TEAM MEMBERS
## MEMBER 1: 210050082
## MEMBER 2: 210050070
## MEMBER 3: 210010076


from z3 import *
import sys

def decimalToBinary(n):
    return bin(n).replace("0b", "")

file = sys.argv[1]

with open(file) as f:
	n,T = [int(x) for x in next(f).split()]
	matrix = []
	for line in f:
		matrix.append([int(x) for x in line.split()])

s = Solver()

# Set s to the required formula

size = len(decimalToBinary(n - 1))

# pos is a 4D array, pijkt means at number k is at ith row, jth column at t th iteration
pos = []
for i in range(n):
	pos.append([])
	for j in range(n):
		pos[i].append([])
		for k in range(size): # change
			pos[i][j].append([])
			for t in range(T+1):
				pos[i][j][k].append([])
				temp = Bool("p{}_{}_{}_{}".format(i,j,k,t))
				pos[i][j][k][t] = temp

# creating array for shifts
rowr = []
rowl = []
colu = []
cold = []
for i in range(n):
	rowr.append([])
	rowl.append([])
	colu.append([])
	cold.append([])
	for j in range(T):
		rowr[i].append([])
		rowl[i].append([])
		colu[i].append([])
		cold[i].append([])

		temp = Bool("r{}_r{}".format(i,j))
		rowr[i][j] = temp

		temp = Bool("r{}_l{}".format(i,j))
		rowl[i][j] = temp

		temp = Bool("c{}_u{}".format(i,j))
		colu[i][j] = temp

		temp = Bool("c{}_d{}".format(i,j))
		cold[i][j] = temp

# Add Initial conditions
for i in range(n):
	for j in range(n): # change
		temp = decimalToBinary(matrix[i][j] - 1).zfill(size)
		for k in range(len(temp)):
			if temp[k] == '1':
				s.add(pos[i][j][matrix[i][j] - 1][0])
			else:
				s.add(Not(pos[i][j][matrix[i][j] - 1][0]))
		

# Final conditions to be met
for i in range(n):
	for j in range(n):  # change
		temp = decimalToBinary(i*n+j).zfill(size)
		for k in range(len(temp)):
			if temp[k] == '1':
				s.add(pos[i][j][i*n+j][T])
			else:
				s.add(Not(pos[i][j][i*n+j][T]))

# Valid cell condition
# for t in range(T+1):
# 	for i in range(n):
# 		for j in range(n):
# 			tempc=[]
# 			for k in range(n*n):
# 				tempc.append((pos[i][j][k][t],1))
# 			s.add(PbEq(tempc,1))

# Across cells pattern is unique
for t in range(T+1):
	for i in range(n):
		for j in range(n):
			for p in range(n):
				for q in range(n):
					if(not( p==i and q== j)):
						temp=[]
						for k in range(size):
							temp.append(Xor(pos[i][j][k][t], pos[p][q][k][t]))
						s.add(Or(*temp))
						
# Pattern must be valid 
#yet to be done
							


# Only 1 max movement condition
for t in range(T):
	temp = []
	for m in range(n):
		temp.append((rowr[m][t],1))
		temp.append((rowl[m][t],1))
		temp.append((colu[m][t],1))
		temp.append((cold[m][t],1))
	s.add(PbLe(temp,1))

# Update after true movement conditions
for m in range(n):
	for t in range(T):
		temp1 = []
		temp2 = []
		temp3 = []
		temp4 = []
		for j in range(n):
			for k in range(n*n):
				temp1.append(pos[m][j][k][t]==pos[m][(j+1)%n][k][t+1])
				temp2.append(pos[m][j][k][t]==pos[m][(n+j-1)%n][k][t+1])
				temp3.append(Implies(pos[j][m][k][t]==pos[(n+j-1)%n][m][k][t+1]))
				temp4.append(Implies(pos[j][m][k][t],pos[(j+1)%n][m][k][t+1]))		
		s.add(Implies(rowr[m][t],And(*temp1)))
		s.add(Implies(rowl[m][t],And(*temp2)))
		s.add(Implies(colu[m][t],And(*temp3)))
		s.add(Implies(cold[m][t],And(*temp4)))

for t in range(T):
	for i in range(n):
		for j in range(n):
			temp=[]
			for k in range(n*n):
				temp.append(Implies(pos[i][j][k][t], pos[i][j][k][t+1]))
			s.add(Implies(And(Not(rowr[i][t]), Not(rowl[i][t]), Not(colu[j][t]), Not(cold[j][t])), And(*temp)))

#print(s)		
x = s.check()
# print(x)
if x == sat:
	print("sat")
	m = s.model()
	for t in range(T):
		for i in range(n):
			if m[rowr[i][t]] :
				print("{}{}".format(i,'r'))
				break
			elif m[rowl[i][t]] :
				print("{}{}".format(i,'l'))
				break
			elif m[colu[i][t]] :
				print("{}{}".format(i,'u'))
				break
			elif m[cold[i][t]] :
				print("{}{}".format(i,'d'))
				break
	

else:
	print("unsat")

	
# 	# Output the moves