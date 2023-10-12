export codimension
export system_of_parameters
export adjugate
export pseudo_diff
export pseudo_diff_helper
export appearing_primefactors # appearing_primefactors
export generate_L1
export integer_generator
export interesting_primes
export replace_coeffs
export hasse_deriv
export ideal_diff
export ideal_diff_all

export loc_greq_2
export loc_greq_b
export is_regular

export MaxOrd
export MaxOrdArith

export hybrid_smoothness_test
export delta_check
#export descend_embedding_smooth
#export embedded_jacobian

####################################################################################
#####################   CODIMENSION OF AN IDEAL   ##################################
# Name:		codimension(I)
#
# INPUT:	Ideal I 
# OUTPUT:	Dimension of I

function codimension(I)
  R = base_ring(I)
  if base_ring(R) == ZZ	# polynomial ring defined over ZZ
    return (codim(I) + 1)
  else  # polynomial ring defined over a field
    return (codim(I))
  end
end

####################################################################################
#####################   SYSTEM OF PARAMETERS   ##################################### 
# Name:		system_of_parameters
#
# INPUT:	
# OUTPUT:	

# es genügt diese einfache Variante von system_of_parameters, da eine triviale Korrespondez zwischen colIndices und dem Parametersystem existiert
function system_of_parameters(R, colIndices)
  systemOfParameters = [gens(R)[i] for i in 1:ngens(R) if i in colIndices]
  return systemOfParameters
end

function system_of_parameters(R, member::Int64, colIndices, coDimZ::Int64)

  n = ngens(R)
  systemOfParameters = empty(gens(R))
  # Bestimme y ueber colIndices, die nicht in Spaltenvector[Spaltennummer] benutzt werden  
  NumbColIndices = length(colIndices)
  NumbSpaltenvectorM = member % NumbColIndices # Zugrundeliegender Spaltenvektor aus JZ
  NumbSpaltenvectorM == 0 && (NumbSpaltenvectorM = NumbColIndices)
  Spaltenvector = colIndices[NumbSpaltenvectorM]  

  for j in 1:n
    equal = 0
    for k in 1:coDimZ
      j == Spaltenvector[k] && (equal = 1)
    end
    equal == 0 && push!(systemOfParameters, gens(R)[j])
  end
  return (systemOfParameters)
end

####################################################################################
#####################   ADJUGATE MATRIX   ########################################## 
# Name:		adjugate
#
# INPUT:	square matrix M 
# OUTPUT:	adjugate matrix of M

# function provided by Max Horn. Thx
function adjugate(M)
  c = charpoly(M)
  f = divexact(c - c(0), gen(parent(c)))
  a = f(M)
  iseven(nrows(M)) ? -a : a
end

####################################################################################
##################   DERIVATE WITH RESPECT TO PARAMETERSYSTEM   ####################
# Name:		pseudo_diff
#
# INPUT:	
# OUTPUT:	

function pseudo_diff(f, j, A, q, I::Ideal, systemOfParameters::Vector)
  R = base_ring(I)

  # Check for correct input? No, it'll be checked in main functions.
  gensR = gens(R)
  RetPoly = q * derivative(f, systemOfParameters[j])

  # Generating a list of Variables which aren't in parametersystem y
  OtherVars = empty(gensR)
  n = ngens(R)
  for k in 1:n
    gensR[k] in systemOfParameters || push!(OtherVars, gensR[k])
  end

  # See formular in remark 4.2
  for k in 1:ncols(A)
    for l in 1:nrows(A)
      SubPoly = derivative(gens(I)[l], systemOfParameters[j]) * A[l,k] * derivative(f, OtherVars[k])
      RetPoly = RetPoly - SubPoly
    end
  end
  Istd = standard_basis(I)
  RetPoly = reduce(RetPoly, gens(Istd)) # mod IZ
  return (RetPoly)
end

# slightly different to be used in delta_check
function pseudo_diff_helper(f, j, A, q, I::Ideal, systemOfParameters::Vector)
  R = base_ring(I)

  # Check for correct input? No, it'll be checked in main functions.
  gensR = gens(R)
  Istd = standard_basis(I) # could be skippable

  RetPoly = q * derivative(f, systemOfParameters[j])

  # Generating a list of Variables which aren't in parametersystem y
  OtherVars = empty(gensR)
  n = ngens(R)
  for k in 1:n
    gensR[k] in systemOfParameters || push!(OtherVars, gensR[k])
  end

  # See formular in remark 4.2
  for k in 1:ncols(A)
    for l in 1:nrows(A)
      SubPoly = derivative(gens(I)[l], systemOfParameters[j]) * A[l,k] * derivative(f, OtherVars[k])
      RetPoly = RetPoly - SubPoly
    end
  end
  return (RetPoly)
end

####################################################################################
#####################   PRIMEFACTORS    ############################################
# Name:		appearing_primefactors
#
# INPUT:	ganze Zahl n (Aktuell für Int64 und fmpz. TODO: fmpz_poly)
# OUTPUT:	Vector der Primfaktoren von n

# returns a 3-element vector containing (1) a vector of appearing primefactors, (2) a vector of their exponents, (3) sign(N) 
function appearing_primefactors(N)
  factors = factor(N)
  u = unit(factors)
  F = sort(collect(factors))
  return ([f[1] for f in F], [f[2] for f in F], u)
end

# to get a vector of all prime factors of the coefficients of all generators of an ideal
function appearing_primefactors(I::Ideal)
  returnList = empty([zero(base_ring(base_ring(I)))])
  for g in gens(I)
    for c in coefficients(g)
      returnList = union(returnList, appearing_primefactors(c)[1])
      #println("# "returnList)
    end
  end
  return sort(returnList)
end

####################################################################################
#####################   GENERATE L1    ############################################
# Name:		generate_L1
#
# INPUT:	
# OUTPUT:	

# returns all submatricies M with det(M) != 0
# for using in delta_check
function generate_L1(IZ::Ideal, IX::Ideal)
  R = base_ring(IZ)
  coDimZ = codimension(IZ)
  JZ = transpose(jacobi_matrix(gens(IZ)))
  maxcol = ncols(JZ)
  maxrow = nrows(JZ)
  colIndices_makeMatrix = AbstractAlgebra.combinations(1:maxcol, coDimZ) # Indices der Spaltenvektoren der Untermatrix
  colIndices = reverse(AbstractAlgebra.combinations(1:maxcol, maxcol-coDimZ)) # Indices der Spaltenvektor, die nicht die Untermatrix bilden
  # generate submatricies # corresponting entries of colIndices and subMatricies are those i need
  subMatricies = [sub(JZ, Vector{Int64}(1:maxrow), indices) for indices in colIndices_makeMatrix]	
  L1 = empty([subMatricies[1], colIndices[1]])
  detM_zero = true
  for member in 1:length(subMatricies)
    M = subMatricies[member]
    detM = det(M)
    # checking if det(M) = 0 mod IX
    for f in gens(IX)
      if is_zero(mod(detM, f))
        detM_zero = true
        break
      end
      detM_zero = false
    end
    # if det(M) != 0 mod IX, pushing M with indices onto L1
    if !detM_zero
      push!(L1, [subMatricies[member], colIndices[member]])
    end
  end
  return L1
end

function generate_L1(coDimZ::Int64, JZ, IX::Ideal, IZ::Ideal)
  R = base_ring(IZ)
  maxcol = ncols(JZ)
  maxrow = nrows(JZ)
  colIndices_makeMatrix = AbstractAlgebra.combinations(1:maxcol, coDimZ) # Indices der Spaltenvektoren der Untermatrix
  colIndices = reverse(AbstractAlgebra.combinations(1:maxcol, maxcol-coDimZ)) # Indices der Spaltenvektor, die nicht die Untermatrix bilden
  # generate submatricies # corresponting entries of colIndices and subMatricies are those i need
  subMatricies = [sub(JZ, Vector{Int64}(1:maxrow), indices) for indices in colIndices_makeMatrix]	
  L1 = empty([subMatricies[1], colIndices[1]])
  IXtemp = IX
  for member in 1:length(subMatricies)
    M = subMatricies[member]
    detM = det(M)
    if detM != zero(R)
      # Ideal_detM = ideal(R, [detM])
      IXtemp = IXtemp + ideal(R, [detM])
      push!(L1, [subMatricies[member], colIndices[member]])
      if radical_membership(one(R), IXtemp)
        break
      end
    end
  end
  return L1
end

# this it needed to get an covering for interesting_primes
function generate_L1(coDimZ::Int64, JZ, IX::Ideal, IZ::Ideal, primeprod)
  R = base_ring(IZ)
  maxcol = ncols(JZ)
  maxrow = nrows(JZ)
  colIndices_makeMatrix = AbstractAlgebra.combinations(1:maxcol, coDimZ)
  colIndices = reverse(AbstractAlgebra.combinations(1:maxcol, maxcol-coDimZ))
  subMatricies = [sub(JZ, Vector{Int64}(1:maxrow), indices) for indices in colIndices_makeMatrix]	
  L1 = empty([subMatricies[1], colIndices[1]])
  IXtemp = IX + ideal(R, [primeprod])
  for member in 1:length(subMatricies)
    M = subMatricies[member]
    detM = det(M)
    if detM != zero(R)
      IXtemp = IXtemp + ideal(R, [detM])
      push!(L1, [subMatricies[member], colIndices[member]])
      if radical_membership(one(R), IXtemp)
        break
      end
    end
  end
  return L1
end

####################################################################################
#####################   INTEGER GENERATOR   ######################################## 
# Name:		integer_generator
#
# INPUT:	Ideal I
# OUTPUT:	Ideal J, was den Schnitt von I mit dem Ring repräsentiert, über den der Polynomring definiert ist

function integer_generator(I)
  vars = gens(base_ring(I))
  J = eliminate(I, vars)  # eliminiere die Variablen des Polynomrings aus dem Ideal I
  return (J)
end

####################################################################################
#####################   INTERESTING PRIMES    ###################################### 
# Name:		interesting_primes
#
# INPUT:	Ideals IZ and IX
# OUTPUT:	

function interesting_primes(IX::Ideal)
  R = base_ring(IX)
  n = ngens(R)
  Itemp = IX
  Iint = ideal(R, [zero(R)])
  while is_zero(Iint)
    f = gens(Itemp)
    Itemp = Itemp + ideal([derivative(g,i) for i=1:n for g in f])
    Iint = integer_generator(Itemp)
  end
  resultList = appearing_primefactors(leading_coefficient(gens(Iint)[1]))[1]
  return resultList
end

function interesting_primes(IZ::Ideal, IX::Ideal)
  # Checking for correct input. 
  IZ != IX || error("IZ and IX cannot be equal.")
  issubset(IZ, IX) || error("IZ needs to be a subset of IX.")

  is_zero(IZ) && return interesting_primes(IX)

  R = base_ring(IZ)
  # Itemp = IX				# Muss für IZ != <O> geändert werden
  Itemp = ideal(R, [f for f in gens(IX) if !(f in IZ)])
  n = ngens(R)

  Iint = integer_generator(IZ)
  if !is_zero(Iint)
    resultList = appearing_primefactors(leading_coefficient(gens(Iint)[1]))[1]
    return (resultList)
  end 
  resultList = appearing_primefactors(IZ)
  coDimZ = codimension(IZ)
  JZ = transpose(jacobi_matrix(gens(IZ)))
  L1 = generate_L1(coDimZ, JZ, IX, IZ, prod(resultList)) # at this moment resultList only contains the primefactors of the coeffs of gens(IZ)
  # inefficient at the moment

  #gensItemp = empty(gens(IX))
  #for poly in gens(IX)
  #  poly in IZ || push!(gensItemp, poly) # what if IZ = <x1> and IX = <x1, 15*x1> ?
  #end # gensItemp = [Generators of IX but not of IZ] 
  #Itemp = ideal(R, gensItemp)

  for member in 1:length(L1)
    # println("# ", "member ", member)
    systemOfParameters = system_of_parameters(R, L1[member][2])
    # println("# ", "system_of_parameters ready")
    # Iint = ideal(R, [zero(R)])
    M = L1[member][1]
    detM = det(M)
    A = adjugate(M) # transposed cofactor matrix of M
    while is_zero(Iint)
      F = gens(Itemp)
      Itemp = Itemp + ideal(R, [pseudo_diff(f, j, A, detM, IZ, systemOfParameters) for f in F for j in 1:length(systemOfParameters)])
      # KLÄREN: Hier muss doch Itemp verändert werden oder nicht?
      Iint = integer_generator(Itemp + IZ)
      # println("# Itemp = ", Itemp)
    end
    # println("# ", "while finished")
    one(R) in Iint || (resultList = union(resultList, appearing_primefactors(leading_coefficient(gens(Iint)[1]))[1]))
  end
  return (resultList)
end

####################################################################################
#####################   REPLACING COEFFICIENTS   ################################### 
# Name:		replace_coeffs
#
# INPUT:	Ideal I and interger p
# OUTPUT:	Ideal J which has all factors p replaced by a new variable P

function replace_coeffs(I::Ideal, p)  
  R = base_ring(I)
  n = ngens(R)

  # Defining new Ring with P as new variable
  Rp, _ = polynomial_ring(base_ring(R), vcat(symbols(R), [:P]))
  GenList = empty([zero(Rp)])
  for f in gens(I)
    g = evaluate(f, gens(Rp)[1:end-1]) # replace old variables with new variables
    gg = zero(Rp)
    # replaceing prime p with variable P
    for term in terms(g) # spliting up terms in coefficient and monomial
      c = leading_coefficient(term)
      m = monomial(term, 1) # only one term anyway
      e, r = remove(c, p) # e = exponent of p in term, r = c/(p^e)
      gg = gg + r*gens(Rp)[end]^e*m # puzzle terms back together
      # println(r*gens(Rp)[end]^e*m) 
    end
    push!(GenList, gg)
  end
  return (ideal(Rp, GenList))
end

####################################################################################
#####################   HASSE-SCHMIDT DERIVATIVE  (IZ == <0>)  ##################### 
# Name:		hasse_deriv
# 			
# INPUT:	Ideals IZ and IX
# OUTPUT:	List of hasse derivatives until and including <1>

# PROBLEM: Some issues if the Ring IX and IZ are from has a certain name or variable names.

function hasse_deriv(IZ,IX)
  R = base_ring(IZ)

  # Checking for correct input. 
  IZ !== IX || error("IZ and IX cannot be equal.")
  issubset(IZ,IX) || error("IZ needs to be a subset of IX.")
  gens(IZ) == [zero(R)] || error("IZ needs to be the zero ideal.")

  n = ngens(R) # number of variables of R
  r = ngens(IX) # number of generators of IX

  # New ring with y and t  # might use other names for variables to avoid using same names as in R
  # SOLUTION: Don't give them names, just write "_". This way there can't be any problems with double naming. 
  Rtemp, _ = polynomial_ring(base_ring(R), "y" => 1:n, "t" => 1:n)
  # Inklusionsmorphismus vom alten zum neuen Ring 
  F = gens(IX)
  for j in 1:r
    F[j] = evaluate(F[j], gens(Rtemp)[1:n] + gens(Rtemp)[n+1:2n]) # F(x) -> F(y+t)
  end
  # F = [evaluate(F[j], gens(Rtemp)[1:n] + gens(Rtemp)[n+1:2n]) for j in 1:r]

  i=1 
  # QUESTION: Should tempid be an ideal or a list/vector?
  tempid = gens(IX)
  RetList = [IX]
  # RetList = empty([IX])
  varR = vcat(gens(R), ones(ZZRingElem, n)) # TODO: fmpz gibts nicht mehr wenn der dev-tree genutzt wird # fmpz -> ZZRingElem, fmpq -> QQFieldElem

  while i == 1 || tempid != gens(RetList[i-1])  # Comparing ideals was a bad idea # A little loophole: 2nd condition would throw an error at the first iteration but because i==1 is true the 2nd conditions check is skipped.
    for p in F
      for term in terms(p)
        if sum(degrees(term)[n+1:2n]) == i
          tempid = vcat(tempid, [evaluate(term, varR)]) # maybe use vector operations for shorter code?
        end
      end
    end
    i = i + 1
    RetList = vcat(RetList, ideal(R, tempid))
  end
  return (RetList[1:i-1])
end

####################################################################################
#####################   HASSE-SCHMIDT DERIVATIVE  (IZ != <0>)   #################### 
# Name:		hasse_deriv
# 
# INPUT:	Ideals IZ,IX, system of parameters y, matrix M
# OUTPUT:	List of hasse derivatives until and including <1>

function hasse_deriv(IZ,IX,y,M)
  R = base_ring(IZ)
  if IZ == ideal(R, [zero(R)])
    return hasse_deriv(IZ,IX)
  end

  # Checking for correct input. 
  IZ !== IX || error("IZ and IX cannot be equal.")
  issubset(IZ,IX) || error("IZ needs to be a subset of IX.")

  # IZstd = standard_basis(ideal(R, reduce(IX, standard_basis(IZ)))) # why is this returning gens(IZ)
  n = ngens(R) # number of variables of R
  t = ngens(IZ)
  r = ngens(IX) - t # number of generators of IX without number of generators of IZ
  f = empty([R(0)])        
  for poly in gens(IX)
    println("# ", poly)
    poly in IZ || push!(f, poly)
  end # f = [Generators of IX but not of IZ]
  detM = det(M)
  A = adjugate(M)

  Itemp = IX
  RetList = [IX] # List of ideals to return.
  # RetList = empty([IX]) # Maybe we don't need IX as first entry?
  Null = zeros(ZZ, length(y)) 

  L = [[f[i],Null] for i in 1:r]
  old = 0
  cur = r 

  while integer_generator(Itemp) == ideal(R, [zero(R)]) # intersect(Itemp, ZZ) == <0> 
    println("# Intersection(Itemp, ZZ) == <0>")
    println("# old = ", old)
    println("# cur = ", cur)
    for i in old+1:cur # for every f in Itemp without gens(IZ)
      # println("# i = ", i)
      for j in 1:length(y) # for every varialbe of system of parameters y
        # println("# yj = ", y[j], " ")
        ftemp = L[i][1]
        note = copy(L[i][2]) # "copy" is important, otherwise "note" would only be a pointer to L[i][2] and NOT a copy
        note[j] = note[j] + 1
        # normal pseudo_diff divided by faktor a
        ftemp = div(pseudo_diff(ftemp, j, A, detM, IZ, y), R(note[j]))
        if ftemp != zero(R)
          L = push!(L, [ftemp, copy(note)]) # "copy" is important, (see above)
          Itemp = Itemp + ideal(R, ftemp)
        end
        sleep(0.001) # hasse_deriv did not work without letting it sleep (julia-stuff)
        println("# ftemp = ", ftemp, " # note = ", note)
        # println("# L = ", L)
      end
      sleep(0.001) # hasse_deriv did not work without letting it sleep (julia-stuff)
    end
    println("# Itemp before saturation: ", Itemp)
    Itemp = saturation(Itemp, ideal(R, detM)) # saturate with <det(M)> to get rid of the factor q = det(M) we got using pseudo_diff
    println("# Itemp saturated with ", detM, ": ", Itemp)
    RetList = push!(RetList, Itemp)
    old = cur
    cur = length(L)
    sleep(0.001) # hasse_deriv did not work without letting it sleep (julia-stuff)
    # println("# RetList = ", RetList)
  end
  return (RetList)
end

####################################################################################
######################   IDEAL DIFF   ############################################## 
# Name:		ideal_diff(IZ, IX)
# 											
# INPUT:	Two ideals IZ and IX 
# OUTPUT:	A vector with derivatives of generators of IX (excluding zeros)

function ideal_diff(IX::Ideal)
  R = base_ring(IX)
  baseRing = base_ring(R)
  if baseRing == ZZ
    # here im getting ideals where a prime already had been replaced by a new variable P. Hence this is a normal derivation
    return [f for f in minors(jacobi_matrix(gens(IX)), 1) if !(is_zero(f))]
  elseif characteristic(baseRing) == 0
    return [f for f in minors(jacobi_matrix(gens(IX)), 1) if !(is_zero(f))]
  elseif characteristic(baseRing) > 0
    return [f for f in minors(jacobi_matrix(gens(IX)), 1) if !(is_zero(f))]
  else
    return ("How did i get here?")
  end 
end

function ideal_diff(IZ::Ideal, IX::Ideal)
  is_zero(IZ) && return ideal_diff(IX)
  R = base_ring(IZ)
  baseRing = base_ring(R)
  if baseRing == ZZ
    coDimZ = codimension(IZ)
    JZ = transpose(jacobi_matrix(gens(IZ)))
    L1 = generate_L1(coDimZ, JZ, IX, IZ)
    IX_deriv = empty([gens(IX)[1]])
    for member in 1:length(L1)
      M = L1[member][1]
      detM = det(M)
      A = adjugate(M)
      systemOfParameters = system_of_parameters(R, L1[member][2])
      F = [f for f in gens(IX) if !(f in IZ)]
      IX_deriv_temp = [pseudo_diff(f, j, A, detM, IZ, systemOfParameters) for j in 1:length(systemOfParameters) for f in F if !(is_zero(pseudo_diff(f, j, A, detM, IZ, systemOfParameters)))]
      IX_deriv = vcat(IX_deriv, IX_deriv_temp)
    end
    return IX_deriv 
  elseif characteristic(baseRing) >= 0
    coDimZ = codimension(IZ)
    JZ = transpose(jacobi_matrix(gens(IZ)))
    L1 = generate_L1(coDimZ, JZ, IX, IZ)
    IX_deriv = empty([gens(IX)[1]])
    for member in 1:length(L1)
      M = L1[member][1]
      detM = det(M)
      A = adjugate(M) # transposed cofactor matrix of M
      systemOfParameters = system_of_parameters(R, L1[member][2])
      F = [f for f in gens(IX) if !(f in IZ)]
      IX_deriv_temp = [pseudo_diff(f, j, A, detM, IZ, systemOfParameters) for j in 1:length(systemOfParameters) for f in F if !(is_zero(pseudo_diff(f, j, A, detM, IZ, systemOfParameters)))]
      IX_deriv = vcat(IX_deriv, IX_deriv_temp)
      # don't know how to "saturate a vector". Good bye time efficiency. Also: Bye bye units.
      for i in 1:length(IX_deriv) # saturating w.r.t. detM
        IX_deriv[i] = gens(saturation(ideal(R, IX_deriv[i]), ideal(R, [detM])))[1]
      end
    end
    return IX_deriv
  else
    return ("How did i get here?")
  end
end

# INPUT:	Two ideals IZ and IX 
# OUTPUT:	A vector with all derivatives of generators of IX (including zeros)

function ideal_diff_all(IX::Ideal)
  R = base_ring(IX)
  baseRing = base_ring(R)
  if baseRing == ZZ || characteristic(baseRing) >= 0
    return [[derivative(gens(IX)[k], var), k] for k in 1:length(gens(IX)) for var in gens(R)]
  else
    return ("How did i get here?")
  end 
end

function ideal_diff_all(IZ::Ideal, IX::Ideal)
  is_zero(IZ) && return ideal_diff_all(IX)
  R = base_ring(IX)
  baseRing = base_ring(R)
  if baseRing == ZZ
    F = [f for f in gens(IX) if !(f in IZ)]  # all gens of IX not in IZ
    coDimZ = codimension(IZ)
    JZ = transpose(jacobi_matrix(gens(IZ)))
    L1 = generate_L1(coDimZ, JZ, IX, IZ)
    IX_deriv = empty([gens(IX)[1], 1])
    for member in 1:length(L1)
      M = L1[member][1]
      detM = det(M)
      A = adjugate(M)
      systemOfParameters = system_of_parameters(R, L1[member][2])
      IX_deriv_temp = [[pseudo_diff(F[k], j, A, detM, IZ, systemOfParameters), k] for j in 1:length(systemOfParameters) for k in 1:length(F)]
      IX_deriv = vcat(IX_deriv, IX_deriv_temp)
    end
    return IX_deriv
  elseif characteristic(baseRing) >= 0
    # TODO: for loop over generators around 621
    ###
    F = [f for f in gens(IX) if !(f in IZ)]  # all gens of IX not in IZ
    coDimZ = codimension(IZ)
    JZ = transpose(jacobi_matrix(gens(IZ)))
    L1 = generate_L1(coDimZ, JZ, IX, IZ)
    IX_deriv = empty([gens(IX)[1]])
    for member in 1:length(L1)
      M = L1[member][1]
      detM = det(M)
      A = adjugate(M) # transposed cofactor matrix of M
      systemOfParameters = system_of_parameters(R, L1[member][2])
      F = [f for f in gens(IX) if !(f in IZ)]
      IX_deriv_temp = [[pseudo_diff(F[k], j, A, detM, IZ, systemOfParameters), k] for j in 1:length(systemOfParameters) for k in 1:length(F)]
      IX_deriv = vcat(IX_deriv, IX_deriv_temp)
      # don't know how to "saturate a vector". Good bye time efficiency. Also: Bye bye units.
      for i in 1:length(IX_deriv) # saturating w.r.t. detM
        IX_deriv[i][1] = gens(saturation(ideal(R, IX_deriv[i][1]), ideal(R, [detM])))[1]
      end
    end
    return IX_deriv
  else
    return ("How did i get here?")
  end
end

####################################################################################
######################   LOCUS OF ORDER GREATER OR EQUAL 2  ######################## 
# Name:		loc_greq_2
# 											
# INPUT:	Two ideals IZ and IX 
# OUTPUT:	One Ideal representing the locus of order 2

# TODO:	- Funktion mit den Ringen aus der Union Ideal funktionieren
#		- In Quotientenringen muss immer nur nach dem Zähler abgleitet werden 
# Es wird nur die erste Ableitung benötigt. 
# Die erste HS-Ableitung ist identisch zur ersten "normalen" Ableitung.
# - sind in MPolyRing
# - Fall 1: MPolyRing über Körper der Char=0
# - Fall 2: MPolyRing über Körper der Char>0 (via Überladen)
# - Fall 3: MPolyRing über ZZ (via Überladen)

function loc_greq_2(IX::Ideal)
  R = base_ring(IX)
  baseRing = base_ring(R)
  Itemp = IX
  if baseRing == ZZ
    PrimeList = interesting_primes(IX)
    if length(PrimeList) == 0
      Itemp = Itemp + ideal(R, ideal_diff(IX))
    end
    for p in PrimeList
      JX = replace_coeffs(IX, p)

      JX_deriv = ideal_diff(JX)
      Vars = vcat(gens(R), R(p))
      Itemp = Itemp + ideal(R, [evaluate(f, Vars) for f in JX_deriv])
    end
  elseif characteristic(baseRing) == 0
    Itemp = Itemp + ideal(R, ideal_diff(IX))
  elseif characteristic(baseRing) > 1
    Itemp = Itemp + ideal(R, ideal_diff(IX))
  else
    return ("How did i get here?")
  end
  return (ideal(R, collect(standard_basis(Itemp))))
end

function loc_greq_2(IZ::Ideal, IX::Ideal)
  R = base_ring(IZ)
  base_ring(IX) === R || error("IZ and IX need to be defined in the same ring")
  IZ !== IX || error("IZ and IX cannot be equal.")
  issubset(IZ, IX) || error("IZ needs to be a subset of IX.")

  is_zero(IZ) && return loc_greq_2(IX)

  n = ngens(R) # may not be needed
  baseRing = base_ring(R)

  # getting a Itemp = <f_1, ..., f_r>
  Itemp = ideal(R, [f for f in gens(IX) if !(f in gens(IZ))])

  if baseRing == ZZ # base_ring ZZ
    PrimeList = interesting_primes(IZ, IX)
    if length(PrimeList) == 0
      Itemp = Itemp + ideal(R, ideal_diff(IX))
    end
    for p in PrimeList
      JX = replace_coeffs(IX, p)
      JZ = replace_coeffs(IZ, p)

      JX_deriv = ideal_diff(JZ, JX)
      Vars = vcat(gens(R), R(p))
      Itemp = Itemp + ideal(R, [evaluate(f, Vars) for f in JX_deriv])
    end
  elseif characteristic(baseRing) == 0 # char == 0
    Itemp = Itemp + ideal(R, ideal_diff(IZ, IX))
  elseif characteristic(baseRing) >= 1 # char >= 1
    coDimZ = codimension(IZ)
    JZ = transpose(jacobi_matrix(gens(IZ)))
    L1 = generate_L1(coDimZ, JZ, IX, IZ)

    for member in 1:length(L1)
      M = L1[member][1]
      detM = det(M)
      A = adjugate(M) # transposed cofactor matrix of M
      systemOfParameters = system_of_parameters(R, L1[member][2])
      s = length(systemOfParameters)
      Itemp = Itemp + ideal(R, [pseudo_diff(f, j, A, detM, IZ, systemOfParameters) for f in gensItemp for j in 1:s])
      Itemp = saturation(Itemp, ideal(R, detM))
    end
  else
    return ("How did i get here?")
  end
  return (ideal(R, collect(standard_basis(Itemp))))
end

####################################################################################
######################   LOCUS OF ORDER GREATER OR EQUAL b  ######################## 
# Name:		loc_greq_b
# 
# INPUT:	Two ideals IZ and IX and a natural number b. 
# OUTPUT:	Vector of ideals representing the locus of increasing order until order b.

# Note: Es ist nicht sinnvoll im Fall char>0 über loc_greq_2 zu iterieren, da genau die Iterierbarkeit der normalen Ableitung mit der hier notwendigen HS-Ableitung nicht möglich ist.

function loc_greq_b(IZ::MPolyQuoIdeal, IX::MPolyQuoIdeal, b::Int64)
  Mod = modulus(base_ring(IX))

  Rtemp = base_ring(base_ring(IX))
  ftemp = [lifted_numerator(f) for f in gens(IX)]
  IXtemp = ideal(Rtemp, ftemp)
  gtemp = [lifted_numerator(g) for g in gens(IZ)]
  IZtemp = ideal(Rtemp, gtemp)

  RetListtemp = loc_greq_b(IZtemp, IXtemp, b)

  # TODO: RetListtemp umwandeln in Liste von Idealen vom Typ MPolyQuoIdeal

  return RetListtemp

end

function loc_greq_b(IZ::Ideal, IX::Ideal, b::Int64)
  R = base_ring(IZ)

  # Checking for correct input. 
  base_ring(IX) === R || error("IZ and IX need to be defined in the same ring")
  IZ !== IX || error("IZ and IX cannot be equal.")
  issubset(IZ,IX) || error("IZ needs to be a subset of IX.")
  b >= 2 || error("b needs to be greater or equal 2.")

  temp = IX
  retList = [temp]

  char = get_char(R)

  # einfach immer base_ring benutzen?

  # case IZ == <0>
  if IZ == ideal(R,[zero(R)])
    if char == 0
      for i in 1:b-1
        temp = loc_greq_2(IZ,temp)
        if one(R) in temp
          return (retList)
        end
        retList = vcat(retList,[temp])
        # ALTERNATIVE: not checking for one(R) in temp and just always add temp to retList. 
        # And what's about appling standard_basis on a regular basis. Is it worth/necessary?
        # retList = vcat(retList,[temp])
      end
    else
      DiffList = hasse_deriv(IZ,IX) # no iteration needed, hasse_deriv already returns all derivatives
      DiffListL = length(DiffList)
      if DiffListL>=b 
        return (DiffList[1:b])
      else
        # return (vcat(DiffList,[ideal(R,[one(R)]) for i in DiffListL+1:b]))
        return (DiffList)
      end
    end
    return (retList) # Liste zurückgeben der Ideale 
    
  # case IZ != <0>
  else
    return ("No implementation for IZ != <0> yet.")
  end
end

####################################################################################
#####################   CHECKING IF X IS REGULAR    ################################ 
# Name:		is_regular
#
# INPUT:	Ideals IZ and IX 
# OUTPUT:	true/false whether X is/isn't regular

function is_regular(IX::Ideal)
  R = base_ring(IX)
  D_IX = loc_greq_2(IX)

  if one(R) in D_IX
    gensIX = gens(IX)
    IX_deriv_all = empty([gensIX[1], 1])
    if base_ring(R) == ZZ 
      PrimeList = interesting_primes(IX)
      if length(PrimeList) == 0
        IX_deriv_all = ideal_diff_all(IX)
      end
      for p in PrimeList
        JX = replace_coeffs(IX, p)
        JX_deriv_all = ideal_diff_all(JX)
        Vars = vcat(gens(R), R(p))
        # IX_deriv_all = vcat(IX_deriv_all, [evaluate(f, Vars) for f in JX_deriv_all if !(evaluate(f, Vars) in IX_deriv_all)])
        IX_deriv_all = vcat(IX_deriv_all, [[evaluate(JX_deriv_all[i][1], Vars), JX_deriv_all[i][2]] for i in 1:length(JX_deriv_all)])
      end
    else
      IX_deriv_all = ideal_diff_all(IX)
    end
    # finding a linear combination of derivatives that generates 1
    linearCombi = coordinates([IX_deriv_all[i][1] for i in 1:length(IX_deriv_all)], one(R))
    # adding generators of IX to IZ if their derivatives are part of linear combination from above
    for k in 1:rank(parent(linearCombi)) # rank(parent(linearCombi)) conveniently is the same number as length(IX_deriv_all)
      if linearCombi[k] != zero(R) # true for at least one k, otherwise D_IX wouldn't have been <1> in the first place
        IZ = ideal(R, [gensIX[IX_deriv_all[k][2]]])
        return is_regular(IZ, IX)
      end
    end
  else
    return false
  end
end

function is_regular(IZ::Ideal, IX::Ideal)
  R = base_ring(IZ)
  base_ring(IX) === R || error("IZ and IX need to be defined in the same ring")
  issubset(IZ, IX) || error("IZ needs to be a subset of IX.")
  IX == radical(IX) || (IX = radical(IX))

  is_zero(IZ) && return is_regular(IX)
  # base case of the recursion
  IZ == IX && return true
  D_IX = loc_greq_2(IZ, IX)
  one(R) in D_IX || return false
  # gens of IX that aren't in IZ
  gensIX = [f for f in gens(IX) if !(f in gens(IZ))]
  IX_deriv_all = empty([gensIX[1], 1])
  if base_ring == ZZ
    PrimeList = interesting_primes(IZ, IX)
    if length(PrimeList) == 0
      IX_deriv_all = ideal_diff_all(IZ, IX)
    else
      for p in PrimeList
      JX = replace_coeffs(IX, p)
      JZ = replace_coeffs(IZ, p)
      JX_deriv_all = ideal_diff_all(JZ, JX)
      Vars = vcat(gens(R), R(p))
      IX_deriv_all = vcat(IX_deriv_all, [[evaluate(JX_deriv_all[i][1], Vars), JX_deriv_all[i][2]] for i in 1:length(JX_deriv_all)])
      end
    end
  else
    IX_deriv_all = ideal_diff_all(IZ, IX)
  end
  # finding a linear combination of derivatives that generates 1
  linearCombi = coordinates([IX_deriv_all[i][1] for i in 1:length(IX_deriv_all)], one(R))
  # adding generators of IX to IZ if their derivatives are part of linear combination from above
  for k in 1:rank(parent(linearCombi)) # rank(parent(linearCombi)) conveniently is the same number as length(IX_deriv_all)
    if linearCombi[k] != zero(R) # true for at least one k, otherwise D_IX wouldn't have been <1> in the first place
      IZ_new = IZ + ideal(R, [gensIX[IX_deriv_all[k][2]]])
      return is_regular(IZ_new, IX)
    end
  end
end

####################################################################################
#####################   LOCUS OF MAXIMAL ORDER   ################################### 
# Name:		MaxOrd
#
# INPUT:	Ideals IZ and IX 
# OUTPUT:	

function MaxOrd(IZ,IX)
  R = base_ring(IZ)

  base_ring(IX) === R || error("IZ and IX need to be defined in the same ring")
  IZ !== IX || error("IZ and IX cannot be equal.")
  issubset(IZ,IX) || error("IZ needs to be a subset of IX.")

  Itemp = IX
  Imax = ideal(R, [one(R)])

  # case IZ == <0>
  if IZ==ideal(R, [zero(R)])
    maxord = 0
    n = ngens(R)
    while !(one(R) in Itemp)
      Imax = Itemp
      f = gens(Itemp)
      Itemp = Itemp + ideal(R,[derivative(g,j) for g in f for j in 1:n])
      maxord = maxord + 1
    end
    return (maxord, Imax)
    # return (maxord, ideal(R,collect(standard_basis(Imax)))) # standard_basis yes or no?
  # case IZ != <0>
  else
    maxord = 1
    coDimZ = codimension(IZ)
    JZ = transpose(jacobi_matrix(gens(IZ)))
    L1 = generate_L1(coDimZ, JZ, IX, IZ)

    gensItemp = empty(gens(IX))
    for poly in gens(IX)
      poly in IZ || push!(gensItemp, poly)
    end # gensItemp = [Generators of IX but not of IZ]
    Itemp = ideal(R, gensItemp)

    for member in 1:length(L1)
      println("# member = ", member)
      Iold = ideal(R, [zero(R)])
      thisord = 0
      M = L1[member][1]
      detM = det(M)
      A = adjugate(M) # transposed cofactor matrix of M
      systemOfParameters = system_of_parameters(R, L1[member][2])
      s = length(systemOfParameters)

      while !(one(R) in Itemp + IZ)
        println("# Itemp + IZ != <1>")
        Iold = Itemp
        # getting generators of Itemp (F = [f1, ..., fr])
        F = gens(Itemp)
        Itemp = Itemp + ideal(R, [pseudo_diff(f, j, A, detM, IZ, systemOfParameters) for f in F for j in 1:s])
        Itemp = saturation(Itemp, ideal(R, detM))
        thisord = thisord + 1
      end
      # check whether its nessecary to glue components
      if thisord >= maxord
        if thisord == maxord
          Imax = intersect(Imax, Iold) # glue components together
        else	# change maxord and ideal of maxorderlocus
          maxord = thisord
          Imax = Iold
        end
      end
    end
  end
  return (maxord, Imax)
end

####################################################################################
#####################   LOCUS OF MAXIMAL ORDER (ARITH)    ########################## 
# Name:		MaxOrdArith
#
# INPUT:	Ideals IZ and IX 
# OUTPUT:	

function MaxOrdArith(IZ::Ideal, IX::Ideal)
  R = base_ring(IZ)
  # TODO: Check for correct input.
  # TODO: Check for vector copy mistakes.

  # replace coefficients in ZZ with coefficients in QQ in order for MaxOrd to work properly
  MaxOrd0 = MaxOrd(ideal([map_coefficients(QQ, f) for f in gens(IZ)]), ideal([map_coefficients(QQ, f) for f in gens(IX)]))
  maxord = MaxOrd0[1]

  Imax = ideal([map_coefficients(ZZ, f) for f in gens(MaxOrd0[2])]) # Imax = MaxOrd[2] intersect ZZ[x]
  # R = base_ring(IZ) 
  RetList = [[0, Imax]]
  PrimeList = interesting_primes(IZ, IX)
  for p in PrimeList
    # In seperate function: apply construction 4.12 (replace coefficients c by c/p^l*P^l for l maximal), denote by JX, JZ resulting ideals in ZZ[x,P]
    JX = replace_coeffs(IX, p)
    JZ = replace_coeffs(IZ, p)  # for first case it would be equal to <0> anyway
    if IZ == ideal(R, [zero(R)])  # case IZ == <0>
      DiffList = hasse_deriv(JZ, JX)
      # RESOLVED: Muss hasse_deriv hierfür erweitert werden? Wenn ich hier JX und JZ in einem neuen Ring mit Variable P definiere sollte hasse_deriv doch ganz normal durchlaufen, oder nicht? Ja, alles gut! 
      m = length(DiffList)
      # Vars = push!(gens(R), R(p))
      # Alternative:
      Vars = gens(R)
      push!(Vars, R(p))
      for i in 1:m 
        # DiffList[i] = ideal(substitute(DiffList[i],P,p))
        DiffList[i] = ideal(R, [evaluate(f, Vars) for f in gens(DiffList[i])])
      end
      while one(R) in DiffList[m] # R == ZZ[x]
        m = m - 1
      end
      if m >= maxord
        Imax = DiffList[m]
        if m > maxord
          maxord = m
          RetList = [[p, Imax]]
        elseif RetList[1][1] != 0
          RetList = vcat(RetList, [[p, Imax]])
        end
      end

    else  # case IZ != <0>
      coDimZ = codimension(IZ)
      JJZ = transpose(jacobi_matrix(gens(JZ)))
      L1 = generate_L1(coDimZ, JJZ, JX, JZ)
      locord = 1
      for member in 1:length(L1)
        M = L1[member][1]
        # y = system_of_parameters
        systemOfParameters = system_of_parameters(base_ring(JX), L1[member][2])
        DiffList = hasse_deriv(JZ, JX, systemOfParameters, M)
        println("hasse_deriv finished")
        m = length(DiffList)
        Vars = push!(gens(R), R(p))
        for i in 1:m
          DiffList[i] = ideal(R, [evaluate(f, Vars) for f in gens(DiffList[i])])
        end
        println("finished substituting P with p")
        while one(R) in DiffList[m]
          m = m - 1
        end
        println("finished reducing m")
        if m > locord 
          Imax = DiffList[m]
          locord = m
        elseif m == locord
          Imax = intersect(Imax, DiffList[m])
        end
      end
      println("end for")
      if locord >= maxord
        if locord > maxord
          RetList = empty(RetList[1])
          marord = locord
          push!(RetList, [p, Imax])
        elseif RetList[1][1] == 0 
          push!(RetList, [p, Imax])
        end
      end
    end
  end
  return (maxord, RetList)
end

####################################################################################
#####################   HYBRID SMOOTHNESS TEST   ################################### 
# Name:		hybrid_smoothness_test
#
# INPUT:	Ideals IZ = <f_1, ..., f_r> subset of IX = <f_1, ..., f_s> element k[x_1, ..., x_n] and a polynomial q, non-negative integer c 
# OUTPUT:	 true if V(IX intersect D(q)) is smooth, false otherwise

function hybrid_smoothness_test(IZ::Ideal, IX::Ideal, q, c)
  if dim(IZ) - dim(IX) == 0
    return true
  end
  if dim(IZ) - dim(IX) <= c
    return embedded_jacobian(IZ, IX, q)
  end
  if !(delta_check(IZ, IX, q))
    return false
  end
  L = descend_embedding_smooth(IZ, IX, q)
  for l in L 
    if !(hybrid_smoothness_test(l[1], l[2], l[3], c))
      return false
    end
  end
  return true
end

####################################################################################
#####################   DELTA CHECK for affine charts  ############################# 
# Name:		delta_check
#
# INPUT:	Ideals IZ = <f_1, ..., f_r> subset of IX = <f_1, ..., f_s> element k[x_1, ..., x_n] and a polynomial q
# OUTPUT:	 true if Sing(I_{X,Z}, 2) intersect D(q) = empty set, false otherwise

function delta_check(IZ::Ideal, IX::Ideal, q)
  # First handle the case IZ=<0>, q=1; then x_1, ..., x_n induce a local
  # system of parameters at every point of Z 
  R = base_ring(IZ)
  if is_zero(IZ) && q == R(1)
    if one(R) in IX + ideal(R, ideal_diff(IX))
      return true
    else
      return false
    end
  end
  # Initialization
  Q = ideal(R, [zero(R)])
  L1 = generate_L1(IZ, IX)
  # F contains all gens(IX)\gens(IZ)
  F = empty(gens(IX))
  for f in gens(IX)
    f in gens(IZ) || push!(F, f)
  end
  # Main loop: Cover by complements of minors
  for member in 1:length(L1) 
    if q in Q
      break
    end
    M = L1[member][1]
    q_new = det(M)
    Q = Q + ideal(R, [q_new])
    A = adjugate(M)
    # Test Sing(I_{X,Z}, 2) subset V(q_new) union V(q)
    systemOfParameters = system_of_parameters(R, L1[member][2])
    s = length(systemOfParameters)
    C_M = IX + ideal(R, [pseudo_diff_helper(f, j, A, q_new, IZ, systemOfParameters) for f in F for j in 1:s])
    # if q_new * q is not in C_M return false
    if !radical_membership(q_new * q, C_M)
      return false
    end
  end
  return true 
end

####################################################################################
#####################   DESCEND EMBEDDING SMOOTH   ################################# 
# Name:		descend_embedding_smooth
#
# INPUT:	Ideals IZ = <f_1, ..., f_r> subset of IX = <f_1, ..., f_s> element k[x_1, ..., x_n] and a polynomial q
# OUTPUT:	 Triples (IZ_i, IX, q_i)

function descend_embedding_smooth(IZ::Ideal, IX::Ideal, q)
  # Direct descent: no need to find an open covering of V(IX) intersect D(q)

  # Descent by constructing an open covering of V(IX) intersect D(q)
  for i in (ngens(IZ)+1):ngens(IX)
    # ideal generated by (r+1)x(r+1) minors 
  end
end

####################################################################################
#####################   EMBEDDED JACOBIAN   ######################################## 
# Name:		embedded_jacobian
#
# INPUT:	Ideals IZ = <f_1, ..., f_r> subset of IX = <f_1, ..., f_s> element k[x_1, ..., x_n] and a polynomial q
# OUTPUT:	 Triples (IZ_i, IX, q_i)

function embedded_jacobian(IZ::Ideal, IX::Ideal, q)
  R = base_ring(IZ)
  Q = ideal(R, [zero(R)])
  L = generate_L1(IZ, IX)
  # Read off regular system of parameters for non-trivial h 
  indices = empty([1])
  for member in 1:length(L)
    M = L[member][1]
    if is_zero(mod(q, det(M))) # if det(M) divides q
      push!(indices, member) 
      # break # use if only one M with det(M) divides q is enough
    end
  end
  if !is_zero(length(indices)) && (length(indices) != length(L))
    L = L[indices]
  end
  # F contains all gens(IX)\gens(IZ)
  F = empty(gens(IX))
  for f in gens(IX)
    f in gens(IZ) || push!(F, f)
  end
  # Covering by complements of the minors
  for member in 1:length(L) 
    if q in Q
      break
    end
    M = L[member][1]
    q_new = det(M)
    Q = Q + ideal(R, [q_new])
    A = adjugate(M)
    # Jacobian matrix of IX w.r.t. local system of parameters for IZ
    systemOfParameters = system_of_parameters(R, L[member][2])
    ### TODO: Was macht system_of_parameters bei coDimZ > length ?
    s = length(systemOfParameters)
    # get entries for Jacobian matrix
    diffs = empty(gens(IZ))
    for f in F 
      diffs = vcat(diffs, [pseudo_diff_helper(f, j, A, q_new, IZ, systemOfParameters) for j in 1:s])
    end
    # construct (s-r) x (n-r) Jacobian matrix
    n = ngens(R)
    Jac = matrix(R, length(F), s, diffs)
    # c = codim(V(IX) intersect D(q) subset V(IZ) intersect D(q))
    J = IX + ideal(R, minors(Jac, c))
    if !radical_membership(q_new * q, J)
      return false
    end
  end
  return true
end





