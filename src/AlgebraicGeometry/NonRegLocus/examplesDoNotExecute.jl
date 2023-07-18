# EXAMPLE codimension
R, x = polynomial_ring(ZZ, 5, "x")
I = ideal(R, [1-x[1]*x[2]])
codimension(I)  # expected: 1

R, x = polynomial_ring(QQ, 5, "x")
I = ideal(R, [1-x[1]*x[2]])
codimension(I)  # expected: 1

# EXAMPLE system_of_parameters
R, x = polynomial_ring(ZZ, 5, "x")
member = 1
colIndices = [[2,3,4,5]]
coDimZ = 1
system_of_parameters(R,member,colIndices,coDimZ) # working

R, x = polynomial_ring(QQ, 5, "x")
member = 1
colIndices = [[3,4,5]]
coDimZ = 2
system_of_parameters(R,member,colIndices,coDimZ)

# EXAMPLE pseudo_diff
R, x = polynomial_ring(ZZ, 8, "x")
f = x[1]^2 + 3x[2]
j = 2
IZ = ideal(R, [x[2]])
y = system_of_parameters(R, 3, [1,2,3,4,5,6,7,8], 1)
M = matrix(R, 1, 1, [R(1)])
detM = det(M)
A = det(M)*inv(M) # adj(M)
pseudo_diff(f, j, A, detM, IZ, y)

# EXAMPLE primefactors
N = ZZ(70)
primefactors(N)  # expected: [2, 5, 7], [1, 1, 1], 1
M = -4318
primefactors(M)  # expected: [2, 17, 127], [1, 1, 1], -1
L = -2^6 * 3^4 * 5^3
primefactors(L)  # expected: [2, 3, 5], [6, 4, 3], -1

R, (x,y,z) = polynomial_ring(ZZ, ["x","y","z"])
IX = ideal(R, [3x - y + 7z])
primefactors(IX)  # expected: 3, 7

IZ = ideal(R, [x - 4y + 6z])
primefactors(IZ)  # expected: 2, 3

I = ideal(R, [54 + 863x - 2290y])
primefactors(I)  # expected: 2, 3, 5, 229, 863

factor(ZZ(2*3*5*7*11*13*17*19)) # what is this order?!

# EXAMPLE generate_L1
R, (x, y, z) = polynomial_ring(ZZ, ["x", "y", "z"])
IZ = ideal(R, [x^2])
coDimZ = codimension(IZ)
JZ = transpose(jacobi_matrix(gens(IZ)))
IX = IZ + ideal(R, [y])
generate_L1(coDimZ, JZ, IX, IZ, prod(primefactors(IZ)))

R, x = polynomial_ring(QQ, 5, "x")
IZ = ideal(R, [1 - x[1]*x[2], 3 - x[1]*x[3]*x[4]])
IX = IZ + ideal(R, [x[5]^2])
JZ = transpose(jacobi_matrix(gens(IZ)))
coDimZ = codimension(IZ)
generate_L1(coDimZ, JZ, IX, IZ)

# EXAMPLE integer_generator
R, (x, y, z) = polynomial_ring(ZZ, ["x","y","z"], ordering=:deglex)
I = ideal(R, [3x^2, 7y, z, 5])
integer_generator(I)
J = ideal(R, [3x^2, 7y, z])
integer_generator(J)

# EXAMPLE interesting_primes
R, (x,y,z) = polynomial_ring(ZZ, ["x","y","z"])
IX = ideal(R, [3x - y + 7z])
IZ = ideal(R, [x - 4y + 6z])
interesting_primes(IZ, IX)  # error (subset)

R, (x,y,z) = polynomial_ring(ZZ, ["x","y","z"])
IZ = ideal(R, [x - 4y + 6z])
IX = IZ + ideal(R, [3x - y + 7z])
interesting_primes(IZ, IX)  # 2, 3, 7, 11 (returs only 2 and 3 at the moment)

R, (x,y,z) = polynomial_ring(ZZ, ["x","y","z"])
IZ = ideal(R, [z])
IX = IZ + ideal(R, [11^2 + x*y])
interesting_primes(IZ, IX)  # 11 ?

R, (x,y,z) = polynomial_ring(ZZ, ["x","y","z"])
IX = ideal(R, [11*x^4])
IZ = ideal(R, [zero(R)])
interesting_primes(IZ, IX)  # 2, 3, 11

R, (x,y,z) = polynomial_ring(ZZ, ["x","y","z"])
IX = ideal(R, [x^2-5^9*y^3])
IZ = ideal(R, [zero(R)])
interesting_primes(IZ, IX)  # 2

R, x = polynomial_ring(ZZ, 5, "x")
IZ = ideal(R, [zero(R)])
IX = ideal(R, [x[5]^7 + x[3]^3])  # 2, 3
IX = ideal(R, [7*x[1]^5, 12*x[5]^5])  # 2, 3, 5
IX = ideal(R, [x[5]^7])  # 2, 3, 5, 7
interesting_primes(IZ, IX) 

R, x = polynomial_ring(ZZ, 5, "x")
IZ = ideal(R, [x[1]])
IX = IZ + ideal(R, [one(R)])  # empty set
IX = IZ + ideal(R, [15*x[1]])  # working # error  (IZ and IX cannot be equal.)
IX = IZ + ideal(R, [34*x[3]]) # working 
IX = IZ + ideal(R, [7*x[2]^5, 12*x[5]^5]) # working # 2, 3, 5
interesting_primes(IZ, IX)

R, x = polynomial_ring(ZZ, 5, "x")
IZ = ideal(R, [3*x[3]])
IX = IZ + ideal(R, [3])
IX = IZ + ideal(R, [7*x[2]^5, 26*x[5]^5]) # working # 3, 2, 13
interesting_primes(IZ, IX)

R, x = polynomial_ring(ZZ, 5, "x")
IZ = ideal(R, [12*x[4]])
IX = IZ + ideal(R, [3])
IX = IZ + ideal(R, [7*x[2]^5, 26*x[5]^3]) # working # 2, 3, 13
interesting_primes(IZ, IX)

# EXAMPLE replace_coeffs
R,(x,y )=polynomial_ring(ZZ, ["x", "y"])
I = ideal(R, [6x^2 + 10y^3])
p = 2
II = ideal(R, [44x^3 + 48*y^4, 15y^2 + 66x])
replace_coeffs(I, p)

# EXAMPLE hasse_deriv (IZ == 0)
R, x = polynomial_ring(ZZ, 4, "x")
IZ = ideal(R, [zero(R)])
IX = ideal(R, [3*x[2], 4*x[4]^3])
hasse_deriv(IZ, IX)

R, x = polynomial_ring(ZZ, 8, "x")
IZ = ideal(R, [zero(R)])
IX = ideal(R, [5*x[2]*x[4]^2*x[5]])
hasse_deriv(IZ, IX)

# EXAMPLE hasse_deriv (IZ != 0)
R, x = polynomial_ring(ZZ, 4, "x")
IX = ideal(R, [3*x[2],4*x[4]^3])
IZ = ideal(R, [zero(0)])
y = x
M = matrix(R, 1, 1, [R(0)])
hasse_deriv(IZ, IX, y, M) # working, since i call hasse_deriv(IZ, IX) for IZ = 0

R, x = polynomial_ring(ZZ, 4, "x")
IZ = ideal(R, [x[1]])
IX = IZ + ideal(R, [3*x[2], 4*x[4]^3])
y = x[2:4]
M = matrix(R, 1, 1, [R(1)])
hasse_deriv(IZ, IX, y, M) # working 

R, x = polynomial_ring(ZZ, 8, "x")
IZ = ideal(R, [x[1]])
y = x[2:8]
M = matrix(R, 1, 1, [R(1)])
IX = IZ + ideal(R, [x[2]*x[3]]) # working
IX = IZ + ideal(R, [x[2]^2]) # working
IX = IZ + ideal(R, [x[2]^2 + 3]) # working
IX = IZ + ideal(R, [x[2]^2*x[3]]) # working
IX = IZ + ideal(R, [x[4]^5, x[2]*x[3]*x[7]]) # working
hasse_deriv(IZ, IX, y, M)

R, x = polynomial_ring(ZZ, 8, "x")
IZ = ideal(R, [x[1]*x[2] - 1])
y = x[2:8]
M = matrix(R, 1, 1, [x[2]])
IX = IZ # error (IZ and IX cannot be equal.)
IX = IZ + ideal(R, [x[1]]) # working
IX = IZ + ideal(R, [x[3]]) # working
IX = IZ + ideal(R, [x[2]^2]) # working
IX = IZ + ideal(R, [x[3]^2]) # working
IX = IZ + ideal(R, [x[2]*x[3]]) # working
IX = IZ + ideal(R, [x[4]^2*x[3]]) # working
IX = IZ + ideal(R, [x[5]^3, x[6]^4]) # working
IX = IZ + ideal(R, [x[6]^4, 7]) # working
IX = IZ + ideal(R, [x[8]^6]) # working
IX = IZ + ideal(R, [x[3]^3 + x[2]^2]) # not working # expected result might be wrong
IX = IZ + ideal(R, [x[4]^3 + x[6]^4]) # working
hasse_deriv(IZ, IX, y, M)

R, x = polynomial_ring(ZZ, 8, "x")
IZ = ideal(R, [x[1]*x[2] - 1])
y = vcat(x[1], x[3:8])
M = matrix(R, 1, 1, [x[1]])
IX = IZ + ideal(R, [x[2]]) # working
IX = IZ + ideal(R, [x[2], x[3]]) # working
IX = IZ + ideal(R, [x[3]]) # working
IX = IZ + ideal(R, [x[3]^2]) # working
IX = IZ + ideal(R, [x[3]^2 - 5]) # working
IX = IZ + ideal(R, [x[4]^2*x[3]]) # working
IX = IZ + ideal(R, [x[5]^3, x[6]^4]) # working
IX = IZ + ideal(R, [x[2]*x[3]]) # working
IX = IZ + ideal(R, [x[2]*x[3]^2]) # working
IX = IZ + ideal(R, [x[6]^4, 7]) # working
IX = IZ + ideal(R, [x[6]^4]) # working
IX = IZ + ideal(R, [x[3]^3 + x[4]^2]) # working
IX = IZ + ideal(R, [x[3]^3 + x[2]^2]) # working
IX = IZ + ideal(R, [x[4]^3 + x[6]^4]) # working
hasse_deriv(IZ, IX, y, M)

# EXAMPLE loc_greq_2
R, (x, y) = polynomial_ring(QQ, ["x", "y"])
IZ = ideal(R, [zero(R)])
IX = ideal(R, [-x^3+y^2])
loc_greq_2(IZ, IX)  # ideal(y, x^2)
IX = ideal(R, [-x^6 + 3*x^5 - 3*x^4 + x^3 - 3*x^2*y^2 + 3*x*y^2 + y^4 - y^2])
loc_greq_2(IZ, IX)  

R, (x, y) = polynomial_ring(ZZ, ["x", "y"])
IZ = ideal(R, [zero(R)])
IX = ideal(R, [-x^3+y^2])
loc_greq_2(IZ, IX)  # ideal(2*y, y^2, 3*x^2, x^2*y, x^3)

R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"])
IZ = ideal(R, [x*y - 1])
IX = IZ + ideal(R, [z^2])
loc_greq_2(IZ, IX)  # ideal(z, x*y - 1)

R, (x, y, z) = polynomial_ring(ZZ, ["x", "y", "z"])
IZ = ideal(R, [x])
IX = IZ + ideal(R, [-x^3+y^2])
loc_greq_2(IZ, IX)

R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"])
P = ideal(R, [x])
U = complement_of_prime_ideal(P)
Rloc, iota = localization(R, U)
IZ = ideal(Rloc, [zero(Rloc)])
IX = ideal(Rloc, [-y^3+x^2])
loc_greq_2(IZ,IX)  # working

# T, t = polynomial_ring(QQ, "t")
# K, a =  number_field(2*t^2-1, "a")
R, (x, y) = polynomial_ring(QQ, ["x", "y"])
I = ideal(R, [x-1])  # I = ideal(R, [x-1, x-a])
RQ, _ = quo(R, I)
IZ = ideal(RQ, [zero(RQ)])
IX = ideal(RQ, [-y^3+x^2])
loc_greq_2(IZ,IX)  # working

R, (x, y) = polynomial_ring(QQ, ["x", "y"])
I = ideal(R, [x^3-1])
RQ, phi = quo(R, I)
P = ideal(R, [y])
U = complement_of_prime_ideal(P)
RQL, iota = localization(RQ, U) 
IZ = ideal(RQL, [zero(RQL)])
IX = ideal(RQL, [-y^3+x^2])  # RESOVLED: IZ and IX are equal (need to understand why ^^ ) # Need to find an example with IZ != IX 
loc_greq_2(IZ,IX)  # working

# EXAMPLE loc_greq_b
R,(x,y)=polynomial_ring(QQ,["x","y"])
IZ=ideal(R,[zero(R)])
IX=ideal(R,-x^3+y^2)
b=2
loc_greq_b(IZ,IX,b)
b=3
loc_greq_b(IZ,IX,b)

S, (u,v)=polynomial_ring(ResidueRing(ZZ,7),["u","v"])
IX = ideal(S,[u^2-5^8*v^3])
IZ = ideal(S,[zero(R)])
b=3
loc_greq_b(IZ,IX,b)

# EXPAMLE is_regular
R,(x, y) = polynomial_ring(QQ, ["x", "y"])
IZ = ideal(R, [zero(R)])
IX = ideal(R, [-x^3 + y^2])
is_regular(IZ, IX)  # expected: false

R,(x, y, z) = polynomial_ring(QQ, ["x", "y", "z"])
IZ = ideal(R, [zero(R)])
IX = ideal(R, [-x^2 + y]) # expected: true
IX = ideal(R, [x, y^2 - z^2]) # expected: false
IX = ideal(R, [x^2 - y^3, (x + 1)^2 - (y + 1)^2])
is_regular(IZ, IX)  

R, x = polynomial_ring(ZZ, 4, "x")
IX = ideal(R, [3*x[2], 4*x[4]^3])
IZ = ideal(R, [zero(R)])
is_regular(IZ, IX)  # expected: false

R, x = polynomial_ring(ZZ, 4, "x")
IX = ideal(R, [x[2]])
IZ = ideal(R, [zero(R)])
is_regular(IZ, IX)  # expected: true

# EXAMPLE MaxOrd
R, (x, y) = polynomial_ring(QQ, ["x", "y"])
IX = ideal(R, [x^2 - 6*y^3])
IZ = ideal(R, [zero(R)])
MaxOrd(IZ, IX)

R, x = polynomial_ring(QQ, 5, "x")
IZ = ideal(R, [x[1]*x[2] - 1])
IX = IZ + ideal(R, [x[3]]) # working
IX = IZ + ideal(R, [x[3]^2]) # working
IX = IZ + ideal(R, [x[3], x[4]]) # working
IX = IZ + ideal(R, [x[3], x[5]^2]) # working
IX = IZ + ideal(R, [x[3]^3, x[5]^2]) # working
MaxOrd(IZ, IX)

R, (x, y, z, v) = polynomial_ring(QQ, ["x", "y", "z", "v"])
IZ = ideal(R, [x*y - 1])
IX = IZ + ideal(R, [z^2])
MaxOrd(IZ, IX)

# EXAMPLE MaxOrdArith
R, (x,y) = polynomial_ring(ZZ, ["x","y"], ordering=:deglex)
IZ = ideal(R, [zero(R)])
IX = ideal(R, [x^2-6*y^3])
MaxOrdArith(IZ, IX)

R, (v,w,x,y,z) = polynomial_ring(ZZ, ["v","w","x","y","z"], ordering=:deglex)
IZ = ideal(R, [zero(R)])
IX = ideal(R, [x])
IX = ideal(R, [3y])
IX = ideal(R, [7x, 12y^3])
IX = ideal(R, [z^7+x^3]) 
IX = ideal(R, [34x])
IX = ideal(R, [9-w^7])
IX = ideal(R, [9-v^4])
IX = ideal(R, [7-v^4])
IX = ideal(R, [12x^4+7z^3, y^2+19])
MaxOrdArith(IZ, IX)

R, (v,w,x,y,z) = polynomial_ring(ZZ, ["v","w","x","y","z"], ordering=:deglex)
IZ = ideal(R, [1-6x^2*y^3])
IX = IZ + ideal(R, [v^2 + 5*w^3])

MaxOrdArith(IZ, IX)


# TESTING subsets

R, x = polynomial_ring(QQ, 5, "x")
IZ = ideal(R, [1-x[1]*x[2]])
JZ = transpose(jacobi_matrix(gens(IZ)))
maxcol = ncols(JZ)
coDimZ = codim(IZ)
dimZ = dim(IZ)
L = minors(JZ, coDimZ)
# subsets(maxcol, coDimZ)
# subsets(maxcol, dimZ)
reverse(sort(subsets(maxcol, coDimZ)))
reverse(sort(subsets(maxcol, dimZ)))

IZ2 = ideal(R, [1-x[1]*x[2], 3-x[1]*x[3]*x[4]])
JZ = transpose(jacobi_matrix(gens(IZ)))
maxcol = ncols(JZ)
coDimZ = codim(IZ)
dimZ = dim(IZ)
L = minors(JZ, coDimZ)
reverse(sort(subsets(maxcol, coDimZ)))
reverse(sort(subsets(maxcol, dimZ)))


###   testing Types and Unions

function test(I)
	return I
end
function test2(I::Int64)
	return I
end
function test3(I::Float64)
	return I
end
function test4(I::Union{Int64,Float64})
	return I
end

test(1)			# working
test(1.0)		# working
test2(1)		# working
test2(1.0)		# error as intended
test3(1)		# error as intended
test3(1.0)		# working
test4(1)		# working
test4(1.0)		# working