import YM.QCD.Port.Loft
import YM.QCD.Door.Prose
/-! # build the attachment sums. True support tier. Includes dull tags with identically zero value. Note sign in form = -bar psi. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ} {D E:Type*}[Fintype D][Fintype E]{t v q C:ℝ}{b B:ℕ}
abbrev XMark (f:Side):=Option (Support f)
abbrev chipK (x:Site f)(b:ℕ) (G:Land f D E)(i:D)(j:E) : XMark f→ Pulse f→Bundle
 | none=> spoon G x b i j
 | some U=> if U ∈ satZip x b then G i j U else 0

def crease (x:Site f)(b:ℕ)(Y:Pays f D E)(i:D)(j:E):XMark f→ℝ
 | none=> Fork.charge Y x b i j
 | some U=> if U ∈ satZip x b then Y i j U else 0

def punch (x:Site f)(b:ℕ):XMark f→Support f
 | none=> trunkFt x b
 | some U=> insert x U
lemma cared (x:Site f)(b:ℕ)(z:XMark f) : x∈punch x b z:=by
   cases z
   · exact halo_subset b _ (mem_singleton_self _)
   exact mem_insert_self ..
variable {W:Grid f→ArrayL D E} {d:D→Site f}{e:E→Site f}{G:Land f D E}{Y:Pays f D E}
lemma cups (h:Pack d e t v b W q G Y)(x: Site f)(i j b S): Run.Crop (d i) (e j) t (punch x b S) (chipK x b G i j S) (crease x b Y i j S):=by
   cases S
   · exact trimming h ..
   next S=> simp only [punch,chipK,crease]; split
            · exact wider_c (h.crop ..) (Finset.subset_insert ..)
            exact Crop.zero
lemma loop_all (h:Pack d e t v b W q G Y)(x:Site f)(i j B)(U:Grid f) : ∑ k:XMark f,chipK x B G i j k (settled U)= Run.cell (W U) i j:=by
   rw [Fintype.sum_option]; congr 1 -- `simp`
   simp only [chipK,produce h x B i j U,add_right_inj]; simp_rw [ite_apply,Pi.zero_apply, ← sum_filter]; rw [Finset.filter_mem_eq_inter,univ_inter] -- lemma
-- quad slices; hinge

def sale (x i j: Site c) (G:Bundle):Bundle:= (((if x=i then (1:ℂ) else 0)+(if x=j then (1:ℂ) else 0))*((2:ℂ)⁻¹)) • G
lemma sale_spin (x i j:Site c) (f: Site c→Site c→Bundle): sale x i j (f i j)= (((if x=i then (1:ℂ) else 0)+(if x=j then (1:ℂ) else 0))*((2:ℂ)⁻¹)) • f i j:=rfl
lemma sold (x i j:Site c)(f:Bundle):‖sale x i j f‖≤ ‖f‖:=by
  unfold sale; split_ifs <;> norm_num [norm_smul] <;> nlinarith [norm_nonneg f]

def batch (S:Ratio c f)(G:Land f (Site c) (Site c))(x:Site c)(z:XMark f)(b:ℕ)(P: Pulse f): Sheet c:=Matrix.of fun i j=> sale x i.1 j.1 (chipK (S.embed x) b G i.1 j.1 z P) i.2 j.2
lemma stack (M:Ratio c f)(p: Site c)(k:XMark f)(G:Land f (Site c) (Site c))(U: Pulse f)(i j): Run.cell (batch M G p k b U) i j=sale p i j (chipK (M.embed p) b G i j k U):=rfl
lemma framesK {W:Grid f→Sheet c}{S:Ratio c f}{L:Land f (Site c) (Site c)}{Y:Pays f (Site c) (Site c)}(h:Pack S.embed S.embed t v b W q L Y)(U:Grid f)(B:ℕ):
   ∑ x : Site c,∑ z:XMark f,batch S L x z B (settled U)=W U:=by
   ext ⟨i,a⟩ ⟨j,b⟩; simp_rw [Matrix.sum_apply,batch,sale]; simp_rw [Matrix.of_apply,Matrix.smul_apply]
   have he x: ∑ z, (chipK (S.embed x) B L i j z (settled U) a b)= W U (i,a) (j,b):=by
     have hg := congr_fun (congr_fun (loop_all h (S.embed x) i j B U) a) b; rw [Matrix.sum_apply] at hg; exact hg
   simp_rw [smul_eq_mul,← mul_sum,he, ← sum_mul]; simp [sum_add_distrib]; ring

-- trace scalar payload complex ring mapping post extraction
abbrev ModeE (c:Side)(F:ℕ):= Alg (Keys c F)
local notation "A"=> Modes c F

def paleF (F:ℕ)(M:Sheet c):EvenA c F:=⟨form (copies F M), form_plus _⟩
def sparkF (c:Side)(F:ℕ)(s:ℂ):EvenA c F:= s • 1
lemma service (F:ℕ)(c:Side)(s:ℂ): light _ (sparkF c F s)=s • (1:ModeE c F):=by rw [sparkF,map_smul,map_one]
lemma serviceP (F:ℕ)(M:Sheet c): light _ (paleF F M)=form (copies F M):=rfl
lemma lit_eqn (x y:EvenA c F)(h:light _ x=light _ y): x=y:=Subtype.ext h
lemma oneC (x y:Sheet c): paleF F (x+y)=paleF F x+paleF F y:=by apply lit_eqn; rw [map_add]; simp only [serviceP]; rw [(show Lat.copies F (x+y)=Lat.copies F x+ Lat.copies F y from Matrix.blockDiagonal_add (fun _=> x) (fun _=> y)),form_add]
lemma noneC : paleF F (0: Sheet c)=0:=by apply lit_eqn; rw [map_zero,serviceP]; simp [Lat.copies,form,Matrix.blockDiagonal_apply]
lemma groups {J:Type*}(Z:J→Sheet c)(U:Finset J):paleF F (∑ i∈U,Z i)=∑ i∈U,paleF F (Z i):=by
   induction U using Finset.induction_on with
   | empty=>rw [sum_empty,sum_empty]; exact noneC
   | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,oneC,ih]
-- define canonical attachment. scalar and jet later
abbrev Varn (f c:Side):=(Site f×XMark f)⊕ (Site c × XMark f)

def orbitM (s:Ratio c f): Varn f c→Site f:=Sum.elim Prod.fst (s.embed ∘ Prod.fst)

def waxV : Varn f c→ XMark f:= Sum.elim Prod.snd Prod.snd

def payT (s:Ratio c f)(b:ℕ) (x:Varn f c): Support f:= punch (orbitM s x) b (waxV x)

def chalkF (G:Land f (Site f) (Site f))(x:Site f)(z:XMark f)(b:ℕ)(P: Pulse f):ℂ:=((chipK x b G x x z P).trace - (chipK x b G x x z (settled 1)).trace)
variable {j k:ℕ}{L:Flight j k}{J:Plan k}{H:f.val=c.val*L.L.val}{V:St f}{W:ℕ→Atom su 2} {w r:ℝ}
local notation "S"=>sliceL L H
variable (P:Swathe L H V W J w t v r q b)

def sliceF (F B:ℕ): Varn f c→ Grid f→ EvenA c F:= Sum.elim (fun i U=> sparkF c F ((F:ℂ)*(chalkF P.walk i.1 i.2 B (settled U)).re)) (fun i U=> paleF F (-(batch S P.bath i.1 i.2 B (settled U))))
lemma valueW (F B:ℕ) (U:Grid f) {R R':ℝ}{D:ℕ}(h: Species L H w R t v R' D V):
   ∑ j : Varn f c, sliceF P F B j U = sparkF c F ((F:ℂ)*((Real.log (V U).det.re-Real.log (V 1).det.re-Extra.Iteration.action W U:ℝ):ℂ))+paleF F (-(dusk L H J V U)):=by
   rw [Fintype.sum_sum_type]; simp_rw [Fintype.sum_prod_type]; unfold sliceF; simp only [Sum.elim_inl,Sum.elim_inr]; congr 1
   · unfold sparkF chalkF; simp_rw [←sum_smul,← mul_sum, ← Complex.ofReal_sum,← Complex.re_sum,sum_sub_distrib,← Matrix.trace_sum,loop_all P.att]; rw [← freeing h]; congr; rw [Matrix.trace_sum,Matrix.trace_sum, ← sum_sub_distrib, Complex.re_sum]
   rw [← framesK P.arcP U B]; simp_rw [← sum_neg_distrib,groups] -- surprising
end YM.QCD.Port
