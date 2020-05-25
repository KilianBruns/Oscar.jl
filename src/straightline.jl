## Op, Line, Arg

struct Op
    x::UInt64
end

struct Line
    x::UInt64
end

struct Arg
    x::UInt64
end


## constants & predicates

const opmask    = 0xff00000000000000
const argmask   = 0x000000000fffffff
const inputmark = 0x0000000008000000
const cstmark   = 0x0000000004000000
const argshift  = 28 # argmask == 2^argshift - 1


const showop = Dict{Op,String}()

for (i, (op, unary, showchar)) in enumerate([(:assign       , false, "->"),
                                             (:uniminus     , true,  "-"),
                                             (:plus         , false, "+"),
                                             (:minus        , false, "-"),
                                             (:times        , false, "*"),
                                             (:divide       , false, "/"),
                                             (:exponentiate , true,  "^"),
                                             (:keep         , true,  "keep"),
                                             ])
    isop = Symbol(:is, op)
    c = UInt64(i) << (2*argshift)
    if unary
        c |= 0x8000000000000000
    end
    @eval begin
        const $op = Op($c)
        $isop(op::Op) = op === $op
    end
    showop[Op(c)] = showchar
end

isquasiunary(op) = (op.x & 0x8000000000000000) != 0
isunary(op) = isquasiunary(op) & (op != exponentiate)


## raw manips

Line(op::Op, i::Arg, j::Arg) = Line(op.x | i.x << argshift | j.x)

pack(op::Op, i, j) = Line(op, Arg(i), Arg(j))

function unpack(line::Line)
    line = line.x
    op = opmask & line
    j = line & argmask
    i = (line >> argshift) & argmask
    Op(op), Arg(i), Arg(j)
end


## show

function Base.show(io::IO, l::Line)
    op, i, j = unpack(l)
    print(io, op, " :  ", i, " , ", j)
end

Base.show(io::IO, op::Op) = print(io, showop[op])

function Base.show(io::IO, x::Arg)
    if isinput(x)
        print(io, '$', inputidx(x))
    elseif isconstant(x)
        print(io, '+', constantidx(x))
    else
        print(io, ' ', x.x)
    end
end


## SLProgram

mutable struct SLProgram{T}
    cs::Vector{T}       # constants
    lines::Vector{Line} # instructions
    len::Int            # length of result vector
                        # (where to store next result for any new line, minus 1)
    ret::Arg            # result index to return (0 for all)
    f::Ref{Function}    # compiled execution
end

SLProgram{T}() where {T} = SLProgram(T[], Line[], 0, Arg(0), Ref{Function}())
SLProgram() = SLProgram{Union{}}()

# return an input
function SLProgram{T}(i::Integer) where {T}
    p = SLProgram{T}()
    pushfinalize!(p, input(i))
end

SLProgram(i::Integer) = SLProgram{Union{}}(i)

function SLProgram(c::Const{T}) where {T}
    p = SLProgram{T}()
    pushfinalize!(p, pushconst!(p, c.c))
end

function Base.copy!(q::SLProgram, p::SLProgram)
    copy!(q.cs, p.cs)
    copy!(q.lines, p.lines)
    q.len = p.len
    q.ret = p.ret
    q
end

copy_oftype(p::SLProgram, ::Type{T}) where {T} = copy!(SLProgram{T}(), p)

Base.copy(p::SLProgram{T}) where {T} = copy_oftype(p, T)

Base.:(==)(p::SLProgram, q::SLProgram) = p.cs == q.cs && p.lines == q.lines && p.ret == q.ret

constants(p::SLProgram) = p.cs
lines(p::SLProgram) = p.lines

constantstype(p::SLProgram{T}) where {T} = T

# return the (max) number of inputs
function ninputs(p::SLProgram)
    m0 = isinput(p.ret) ? inputidx(p.ret) % Int : 0
    m1 = mapreduce(max, lines(p); init=0) do line
        op, i, j = unpack(line)
        max(isinput(i) ? inputidx(i) : 0,
            isinput(j) ? inputidx(j) : 0) % Int
    end
    max(m0, m1)
end

slpgen(n::Integer) = SLProgram(n)
slpgens(n::Integer) = [SLProgram(i) for i=1:n]
slpcst(c) = SLProgram(Const(c))


## show

# old basic version, useful when normal show is broken
function showsimple(io::IO, p::SLProgram)
    println("SLProgram with constants:")
    for (i, c) in enumerate(constants(p))
        println(io, i, " | ", c)
    end
    println("and with lines:")
    for (i, l) in enumerate(lines(p))
        println(io, i, " | ", l)
    end
    println("return: ", p.ret)
end

showsimple(p::SLProgram) = showsimple(stdout, p)

slpsyms(n::Integer) =
    n <= 3 ?
        (:x, :y, :z)[1:n] :
        (Symbol(:x, i) for i = 1:n)

function Base.show(io::IO, p::SLProgram)
    gs = get(io, :SLPsymbols, slpsyms(ninputs(p)))
    show(io, evaluate(p, lazygens(gs), Const))
end

function Base.show(io::IO, ::MIME"text/plain", p::SLProgram{T}) where T
    n = length(lines(p))
    gs = get(io, :SLPsymbols, slpsyms(ninputs(p)))
    syms = lazygens(gs)
    reslazy = Lazy[]
    if n == 0 && !hasmultireturn(p)
        # trivial program, show only result
        return show(io, retrieve(p.cs, syms, reslazy, p.ret))
    end

    str(x...) = sprint(print, x...; context=io)
    strlines = Vector{String}[]
    widths = [0, 0, 0, 0, 0]

    ptmp = SLProgram{T}()
    copy!(ptmp.cs, p.cs)

    for line in lines(p)
        op, i, j = unpack(line)
        k = updatelen!(ptmp, op, i, j)
        push!(ptmp.lines, line)
        pushfinalize!(ptmp, Arg(k))
        # TODO: add a way to evaluate step by step instead of re-evaluating
        # from the beginning each time
        plazy = evaluate!(reslazy, ptmp, syms, Const)
        # TODO: the following bloc should probably be removed (constants are
        # no more stored in the result array, and we don't want to hide an
        # explicit assign)
        if 1 < k == n && op == assign && i.x == k-1+length(constants(p))
            # 1 < k for trivial SLPs returning a constant
            break
        end
        line = String[]
        push!(strlines, line)
        if iskeep(op)
            push!(line, "keep:")
            if i.x == 0
                push!(line, " nothing")
            elseif i.x == 1
                push!(line, " #1")
            else
                push!(line, " #1..#$(j.x)")
            end
            continue
        end
        push!(line, str('#', string(k), " ="))
        x = showarg(constants(p), syms, i)
        y = isunary(op) || isassign(op) ? "" :
            isquasiunary(op) ? string(j.x) :
            showarg(constants(p), syms, j)

        strop = isassign(op) ? "" : showop[op]
        push!(line, str(strop), x, y, str(plazy))
        widths .= max.(widths, textwidth.(line))
    end
    for (k, line) in enumerate(strlines)
        k == 1 || println(io)
        if line[1] == "keep:"
            join(io, line)
            continue
        end
        print(io, ' '^(widths[1]-length(line[1])), line[1])
        for i = 2:4
            print(io, ' '^(1+widths[i]-textwidth(line[i])), line[i])
        end
        print(io, "  ==>  ", line[5])
    end

    print(io, "\nreturn: ")
    # TODO: ^--- remove when unnecessary?
    if hasmultireturn(p)
        print(io, '[')
        join(io,
             (showarg(constants(p), syms, Arg(i)) for i in 1:p.len),
             ", ")
        print(io, ']')
    else
        print(io, showarg(constants(p), syms, p.ret))
    end

end

function showarg(cs, syms, i)
    if isconstant(i)
        string(cs[constantidx(i)])
    elseif isinput(i)
        string(syms[inputidx(i)])
    else
        "#$(i.x)"
    end
end


## building SLProgram

isregister(i::Arg) = (inputmark | cstmark) & i.x == 0

# return #ref for i-th input
function input(i::Integer)
    i = Int(i)
    @assert i < cstmark
    Arg((i % UInt64) | inputmark)
end

isinput(i::Arg) = inputmark & i.x === inputmark
inputidx(i::Arg) = i.x ⊻ inputmark

isconstant(i::Arg) = cstmark & i.x === cstmark
constantidx(i::Arg) = i.x ⊻ cstmark

asconstant(i::Integer) = Arg(UInt64(i) | cstmark)

hasmultireturn(p::SLProgram) = p.ret.x == 0
setmultireturn!(p::SLProgram) = (p.ret = Arg(0); p)

# call before mutating, unless p is empty (opposite of pushfinalize!)

# TODO: pushinit! & pushfinalize! not really nececessary anymore?
pushinit!(p::SLProgram) = p.ret

function pushconst!(p::SLProgram{T}, c::T) where T
    push!(constants(p), c)
    l = lastindex(constants(p))
    @assert l < cstmark
    asconstant(l)
end

function updatelen!(p, op, i, j)
    if isassign(op) && j != Arg(0)
        ptr = Int(j.x)
    elseif iskeep(op)
        ptr = Int(i.x)
        ptr <= p.len || throw(ArgumentError("cannot `keep` so many items"))
        p.len = ptr
    else
        ptr = p.len += 1
        @assert ptr < cstmark
    end
    ptr
end

function pushop!(p::SLProgram, op::Op, i::Arg, j::Arg=Arg(0))
    @assert i.x <= argmask && j.x <= argmask
    ptr = updatelen!(p, op, i, j)
    push!(lines(p), Line(op, i, j))
    Arg(ptr % UInt64)
end

function pushfinalize!(p::SLProgram, ret::Arg)
    p.ret = ret
    p
end

function _combine!(p::SLProgram, q::SLProgram)
    i1 = pushinit!(p)
    i2 = pushinit!(q)
    koffset = length(constants(p))
    len = length(lines(p))
    append!(lines(p), lines(q))
    append!(constants(p), constants(q))

    @assert length(constants(p)) < cstmark # TODO: should not be @assert
    for n = len+1:lastindex(lines(p))
        op, i, j = unpack(lines(p)[n])
        if isconstant(i)
            i = Arg(i.x + koffset)
        elseif isinput(i)
        else
            i = Arg(i.x + len)
        end
        if isconstant(j)
            j = Arg(j.x + koffset)
        elseif isinput(j)
        elseif !isquasiunary(op)
            j = Arg(j.x + len)
        end
        lines(p)[n] = Line(op, i, j)
        # TODO: write conditionally only when modifications
    end
    if isconstant(i2)
        i2 = Arg(i2.x + koffset)
    elseif isinput(i2)
    else
        i2 = Arg(i2.x + len)
    end
    p.len += q.len
    i1, i2
end

function combine!(op::Op, p::SLProgram, q::SLProgram)
    i = pushop!(p, op, _combine!(p, q)...)
    pushfinalize!(p, i)
end

function combine!(op::Op, p::SLProgram)
    i = pushinit!(p)
    i = pushop!(p, op, i)
    pushfinalize!(p, i)
end

function combine!(op::Op, p::SLProgram, e::Integer)
    i = pushinit!(p)
    i = pushop!(p, op, i, Arg(UInt64(e)))
    pushfinalize!(p, i)
end


## mutating ops

addeq!(p::SLProgram, q::SLProgram) = combine!(plus, p, q)

subeq!(p::SLProgram, q::SLProgram) = combine!(minus, p, q)

function subeq!(p::SLProgram)
    combine!(uniminus, p)
    p
end

muleq!(p::SLProgram, q::SLProgram) = combine!(times, p, q)

function expeq!(p::SLProgram, e::Integer)
    combine!(exponentiate, p, e)
    p
end


## unary/binary ops

copy_jointype(p::SLProgram, q::SLProgram) =
    copy_oftype(p, typejoin(constantstype(p), constantstype(q)))

+(p::SLProgram, q::SLProgram) = addeq!(copy_jointype(p, q), q)

*(p::SLProgram, q::SLProgram) = muleq!(copy_jointype(p, q), q)

-(p::SLProgram, q::SLProgram) = subeq!(copy_jointype(p, q), q)

-(p::SLProgram) = subeq!(copy(p))

^(p::SLProgram, e::Integer) = expeq!(copy(p), e)


## conversion Lazy -> SLProgram

SLProgram(l::Lazy) = SLProgram{constantstype(l)}(l)

function SLProgram{T}(l::Lazy, gs=gens(l)) where T
    p = SLProgram{T}()
    i = pushlazy!(p, l, gs)
    pushfinalize!(p, i)
end

pushlazy!(p::SLProgram, l::Const, gs) = pushconst!(p, l.c)

pushlazy!(p::SLProgram, l::Gen, gs) = input(findfirst(==(l.g), gs))

function pushlazy!(p, l::Union{Plus,Times}, gs)
    # TODO: handle isempty(p.xs) ?
    op = l isa Plus ? plus : times
    x, xs = Iterators.peel(l.xs)
    i = pushlazy!(p, x, gs)
    for x in xs
        j = pushlazy!(p, x, gs)
        i = pushop!(p, op, i, j)
    end
    i
end

function pushlazy!(p, l::Minus, gs)
    i = pushlazy!(p, l.p, gs)
    j = pushlazy!(p, l.q, gs)
    pushop!(p, minus, i, j)
end

pushlazy!(p, l::UniMinus, gs) = pushop!(p, uniminus, pushlazy!(p, l.p, gs))

pushlazy!(p, l::Exp, gs) =
    pushop!(p, exponentiate, pushlazy!(p, l.p, gs), Arg(l.e))


## conversion SLProgram -> Lazy

lazygens(gs) = Lazy[Gen(s) for s in gs]
lazygens(n::Integer) = lazygens(slpsyms(n))

# strictly convenience function
aslazy(p::SLProgram, gs=lazygens(ninputs(p))) = evaluate(p, gs, Const)


## evaluate

getres(p::SLProgram, xs) = Vector{eltype(xs)}(undef, length(p.lines))
# length(p.lines) might be an overestimate in some cases, but
# this generally limits the number of allocations

function evaluate(p::SLProgram{T}, xs::Vector{S}, conv::F=nothing
                  ) where {T,S,F}
    if isassigned(p.f)
        p.f[](xs)::S
    else
        evaluate!(getres(p, xs), p, xs, conv)
    end
end

function evaluates(p::SLProgram{T}, xs::Vector{S}, conv::F=nothing
                   ) where {T,S,F}
    res = getres(p, xs)
    evaluate!(res, p, xs, conv)
    res
end

retrieve(cs, xs, res, i) =
    isconstant(i) ? cs[constantidx(i)] :
    isinput(i) ? xs[inputidx(i)] :
    res[i.x]

function evaluate!(res::Vector{S}, p::SLProgram{T}, xs::Vector{S},
                   conv::F=nothing) where {S,T,F}
    # TODO: handle isempty(lines(p))
    empty!(res)

    cs = constants(p)
    for line in lines(p)
        local r::S
        op, i, j = unpack(line)
        if iskeep(op)
            @assert isregister(i)
            resize!(res, i.x)
            continue
        end
        x = retrieve(cs, xs, res, i)
        if isexponentiate(op)
            r = x^Int(j.x) # TODO: support bigger j
        elseif isassign(op)
            r = x
            dst = j.x % Int
            if dst != 0
                res[dst] = x
                continue
            end
        elseif isuniminus(op)
            r = -x
        else
            y = retrieve(cs, xs, res, j)
            if isplus(op)
                r = x + y
            elseif isminus(op)
                r = x - y
            elseif istimes(op)
                r = x * y
            elseif isdivide(op)
                r = divexact(x, y)
            else
                throw(ArgumentError("unknown operation"))
            end
        end
        push!(res, r)
    end

    @assert length(res) == p.len
    if hasmultireturn(p)
        res
    else
        x = retrieve(cs, xs, res, p.ret)
        isa(x, S) ? x : conv(x)
    end
end


## compile!

cretrieve(i) =
    isinput(i) ? Symbol(:x, inputidx(i)) => inputidx(i) :
    isconstant(i) ? Symbol(:c, constantidx(i)) => 0 :
    Symbol(:res, i.x) => 0

# TODO: handle the "conv" argument like in evaluate!
# (works without, but there can be type-instability)

# return compiled execution function f, and updates
# p.f[] = f, which is not invalidated when p is mutated
function compile!(p::SLProgram)
    res = Expr[]
    fn = :(function (xs::Vector)
           end)
    k = 0
    cs = constants(p)
    for k in eachindex(cs)
        push!(res, :($(Symbol(:c, k)) = @inbounds $cs[$k]))
    end
    mininput = 0
    for line in lines(p)
        k += 1
        rk = Symbol(:res, k)
        op, i, j = unpack(line)
        x, idx = cretrieve(i)
        mininput = max(mininput, idx)
        line =
            if isexponentiate(op)
                :($rk = $x^$(Int(j.x)))
            elseif isassign(op)
                :($rk = $x)
            elseif isuniminus(op)
                :($rk = -$x)
            else
                y, idx = cretrieve(j)
                mininput = max(mininput, idx)
                if isplus(op)
                    :($rk = $x + $y)
                elseif isminus(op)
                    :($rk = $x - $y)
                elseif istimes(op)
                    :($rk = $x * $y)
                elseif isdivide(op)
                    :($rk = divexact($x, $y))
                end
            end
        push!(res, line)
    end
    for k = 1:mininput-1
        pushfirst!(res, :($(Symbol(:x, k)) = @inbounds xs[$k]))
    end
    if mininput >= 1
        pushfirst!(res, :($(Symbol(:x, mininput)) = xs[$mininput]))
    end
    append!(fn.args[2].args, res)
    p.f[] = eval(fn)
end
