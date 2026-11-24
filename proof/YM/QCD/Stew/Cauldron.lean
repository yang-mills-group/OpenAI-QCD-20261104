import YM.QCD.Stew.Rove
/-! # gauge-covariant stencil returning affine moments.
Always work in lattice sites at one scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
open Revolve Flume Quarry
open AnalyticBridge.VerifiedReset
-- stencil R at o, maps both moment weights independently. clock index abbreviation as product.
abbrev SampleX := Option (Axis× Bool)
def mark (o : Site c)(a:SampleX)(i j: Site c):ℂ:= a.elim 1 (fun b=> (lift ((if b.2 then j else i)-o) b.1:ℂ))
abbrev coordinates (X:Sheet c)(i j : Site c): Spike:= gold (cell X i j)
def shape (o: Site c)(X:Sheet c)(s: SampleX): Spike:=∑ i,∑ j,(shine o i * shine o j* mark o s i j) • gold (cell X i j)
def delta (U:Grid c)(p:Axis): Sheet c:=(2:ℂ)⁻¹ • (Lat.shift 0 U p-star (Lat.shift 0 U p))
def localX (o:Site c)(M:Spike): Sheet c:= rides (Equiv.refl _) (fun i=> if o=i then wave M else 0)
def entry (o:Site c)(M:Spike)(i:SampleX)(U: Grid c):Sheet c:=
     i.elim (localX o M) (fun p=> if p.2 then localX o M * delta U p.1 else -delta U p.1 * localX o M)
lemma mark_self (o:Site c)(i:SampleX): mark o i o o=if i=none then 1 else 0:=by cases i<;> simp [mark,lift]
lemma δ_back (U:Grid c)(p:Axis): star (delta U p)= -delta U p:=by unfold delta; simp only [star_sub,star_smul,star_inv₀,star_ofNat,star_star]; rw [← neg_sub,smul_neg]
lemma localStar (o:Site c)(M:Spike): star (localX o M)=localX o (star M):=by unfold localX; rw [ride_ad]; congr 1; funext s; by_cases hp:o=s<;> simp [hp,wave_star]
lemma hero (U:Grid c)(o:Site c)(M:Spike)(p:Axis):entry o M (some (p,false)) U=star (entry o (star M) (some (p,true)) U):=by change - delta U p * localX o M=star (localX o (star M)* delta U p); rw [star_mul,localStar,star_star,δ_back]
lemma board (s:Equiv.Perm (Site c))(K: Site c→Bundle)(i j): cell (rides s K) i j=if s i=j then K i else 0:=by ext u v; change (if s i=j then _ else _) =_; split <;> rfl
lemma placed (o i j: Site c)(X:Spike): cell (localX o X) i j=if i=j∧ i=o then wave X else 0:=by unfold localX; rw [board]; by_cases h:i=j <;> by_cases h':i=o<;> simp [h,h', eq_comm]
lemma solid (o:Site c)(A B:Sheet c)(s:SampleX): shape o (A+B) s = shape o A s+shape o B s:=by
    have he (i j):gold (cell (A+B) i j)=gold (cell A i j)+ gold (cell B i j):=rfl -- inspect
    unfold shape; simp_rw [he,smul_add,sum_add_distrib]
lemma metallic (o:Site c)(A:Sheet c)(t:ℂ)(s:SampleX): shape o (t • A) s=t • shape o A s:=by
    have he(i j): gold (cell (t • A) i j)=t • gold (cell A i j):=rfl
    unfold shape; simp only [he,Finset.smul_sum]; simp_rw [smul_comm _ t]
def invert (s:SampleX): SampleX:= s.map fun i=>(i.1,!i.2)
@[simp] lemma inv_inv (s:SampleX): invert (invert s)=s:=by cases s<;> simp [invert]
lemma chess (o:Site c)(X: Sheet c)(p:SampleX): shape o (star X) (invert p)=star (shape o X p):=by
   unfold shape; rw [sum_comm, star_sum]; refine sum_congr rfl fun i _=>?_ ; rw [star_sum]; refine sum_congr rfl fun j _=> ?_
   rw [star_smul]; apply congr_arg₂ (· • ·)
   · have hx : shine o j*shine o i= star (shine o i*shine o j):=by obtain h|h:=shines o j <;> obtain h'|h':=shines o i<;> simp [h,h']
     rw [star_mul (shine o i*shine o j), hx, mul_comm]; apply congr_arg₂ _ _ rfl; unfold invert mark; cases p; · simp
     next p=> rcases p with ⟨a,_|_⟩<;> simp
   rw [show cell (star X) j i=star (cell X i j) from cell_flip ..]; rfl
lemma gold0: gold 0=0:=rfl
lemma atO (o:Site c)(X:Spike)(s:SampleX): shape o (localX o X) s=if s=none then X else 0 :=by
   unfold shape; rw [sum_eq_single o]; rotate_left
   · intro i _ hi; refine sum_eq_zero fun j _=>?_ ; rw [placed,if_neg (fun h=>hi h.2),gold0, smul_zero]
   · simp
   rw [sum_eq_single o,placed,if_pos ⟨rfl,rfl⟩, shine_self, mark_self,leafy]; split <;> simp
   · intro j _ hj; rw [placed,if_neg (fun h=> hj h.1.symm),gold0, smul_zero]
   simp
end YM.QCD.Stew
