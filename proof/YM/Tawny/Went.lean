import YM.Tawny.Mode
/- Generic complex upper money transfer. Important using real conjug here NOT F. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Offer
open Labels Function Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {I:Type}{G : Gauge}{d : ℕ}
-- ℂ Family memory using arbitrary coordinate permutations. I=Axis×
variable (K:Signed→ I → I)(A:Signed→ I→ℝ)
def spectral : Submodule ℂ (I→ Label G d) where
 carrier := {x| ∀ s:Signed,∀ i:I,tensor s.ortho (x i)=(↑(A s i):ℂ) • x (K s i)}
 add_mem':=by intro x y h k s i; change tensor _ (x i+y i)=_ • (x _+y _); rw[map_add,h,k,smul_add]
 zero_mem':=by intro s i; change tensor _ 0=_ • 0; rw [map_zero,smul_zero]
 smul_mem':=by intro z x h s i; change tensor _ (z • x i)=_ • z • x (K s i); rw [map_smul,h,smul_comm]
local notation "S"=>spectral (G:=G) (d:=d) K A

def spectralR : Submodule ℝ (I→Label G d) where
 carrier:={x| x∈ S ∧∀ i:I, realBar (x i)=x i}
 add_mem':=by intro x y ⟨h,t⟩ ⟨k,u⟩; refine ⟨(S).add_mem h k,fun i=>?_⟩; simp only [Pi.add_apply,map_add,t,u]
 zero_mem':= ⟨Submodule.zero_mem _,fun i=>map_zero _⟩
 smul_mem':=by intro z x ⟨h,t⟩; refine ⟨?_,fun i=>?_⟩; rw [← Complex.coe_smul z]; exact (S).smul_mem _ h
               simp only [Pi.smul_apply,← Complex.coe_smul z,map_smulₛₗ,t]; simp
local notation "R'"=> spectralR (G:=G) (d:=d) K A
variable (x:spectral (G:=G) (d:=d) K A)
noncomputable def splitR (x:S)(i:I) := ((2:ℝ)⁻¹ • ((x.val i)+ realBar (x.val i)))
open Complex
local notation "P"=>S
lemma realS : splitR K A x∈R':=by
     constructor
     · intro s i; change spinR s _= (A s i) • _; have he :spinR s (x.val i) = (A s i) • (x.val (K s i)):= x.property s i
       have ht : spinR s (realBar (x.val i))=realBar (spinR s (x.val i)):= Eq.symm (real_turn s.ortho _)
       rw [splitR,splitR,map_smul,map_add,ht,he, realBar_scale]; rw[← smul_add,smul_comm]
     intro i; rw[splitR,realBar_scale, map_add, twice,add_comm]; -- rhs?
noncomputable def coinR : S→ₗ[ℝ] R' where
  toFun x:=⟨splitR K A x,realS ..⟩
  map_add' x y:= Subtype.ext (funext fun i=>by change splitR K A _ _=splitR K A _ i+splitR K A _ i; unfold splitR; simp only [Submodule.coe_add, Pi.add_apply,map_add,smul_add]; abel)
  map_smul' r x:= Subtype.ext (funext fun i=>by change splitR K A _ _=r • splitR K A _ i; unfold splitR; change ((2:ℝ)⁻¹ • (r • _+ realBar (r • _)))= r • ((2:ℝ)⁻¹ • ((x.val i)+_)); rw [realBar_scale,← smul_add,smul_comm])
-- Lean needs [Module ℝ S]; restrictScalars inferred? submodule ℂ ℝ.has
local notation "L" => coinR K A
local notation "Z"=> (-Complex.I) • x
lemma spun (i:I) : x.val i=splitR K A x i + Complex.I • (splitR K A (Z) i):=by
     let u:= x.val i; let v:= realBar u; have ht (y:Label G d) : (2:ℝ)⁻¹ • y=(2:ℂ)⁻¹ • y:=by rw [← IsScalarTower.algebraMap_smul ℂ (2:ℝ)⁻¹,map_inv₀,map_ofNat]
     change u=(2:ℝ)⁻¹ • (u+v)+ Complex.I • ( (2:ℝ)⁻¹ • ((-Complex.I) • u+realBar ((-Complex.I) • u))); rw [map_smulₛₗ, show starRingEnd ℂ (-Complex.I)=Complex.I from by simp,ht,ht]
     rw[smul_add (2:ℂ)⁻¹,smul_add (2:ℂ)⁻¹,smul_add,smul_comm Complex.I (2:ℂ)⁻¹,smul_comm Complex.I (2:ℂ)⁻¹ (Complex.I • _),smul_smul Complex.I (-Complex.I),smul_smul Complex.I Complex.I, mul_neg,I_mul_I,neg_neg,neg_one_smul,one_smul]; module
lemma surri [Fintype I] : Module.finrank ℂ S ≤ Module.finrank ℝ (R'):=by
     haveI: FiniteDimensional ℝ S:=Module.Finite.trans ℂ _; haveI FI: FiniteDimensional ℝ (Label G d):=Module.Finite.trans ℂ _
     let M:S →ₗ[ℝ] S:= (((-Complex.I) • (LinearMap.id (M:=S) (R:=ℂ))).restrictScalars ℝ)
     let Q : S→ₗ[ℝ] (R'× R'):= (L).prod ((L).comp M)
     have ht:Injective Q:=by
          intro x y h; apply Subtype.ext; funext i; rw[spun K A x,spun K A y]; apply congr_arg₂ (·+·)
          · exact congr_fun (congr_arg Subtype.val (congr_arg Prod.fst h)) i
          apply congr_arg (Complex.I • ·); exact congr_fun (congr_arg Subtype.val (congr_arg Prod.snd h)) i
     haveI: Module.Free ℂ ↥S:=Module.Free.of_divisionRing ℂ ↥S; haveI : Module.Free ℝ ↥(R'):=Module.Free.of_divisionRing ℝ ↥(R'); have he:= LinearMap.finrank_le_finrank_of_injective ht; have hi := Module.finrank_mul_finrank ℝ ℂ ↥S; rw [← hi,Complex.finrank_real_complex,Module.finrank_prod] at he; omega

noncomputable abbrev marks (s:Signed)(u:Axis×Axis):= sign s u.1*sign s u.2
abbrev acts (s:Signed)(u:Axis×Axis):= ((s.perm u.1),(s.perm u.2))
abbrev TwoG (G:Gauge) := spectral (G:=G) (d:=4) acts marks
noncomputable abbrev Vc (s:Signed)(i:Axis):Axis:= s.perm i
abbrev OneG (G:Gauge):= spectral (G:=G) (d:=5) Vc sign
local notation "TT"=> spectralR (G:=G) (d:=4) acts marks
local notation "VT"=> spectralR (G:=G) (d:=5) Vc sign
noncomputable def binder : TT →ₗ[ℝ] RawAny G where
 toFun x:=⟨fun a b=>x.val (a,b), fun a b=>x.property.2 _,fun s a b=>x.property.1 s (a,b)⟩ -- coe_smul issue
 map_add' x y:=rfl
 map_smul' x y:=rfl
noncomputable def binderV : VT →ₗ[ℝ] RawOne G where
 toFun x:= ⟨x.val,x.property.2,x.property.1⟩
 map_add' x y:=rfl
 map_smul' r x:=rfl
lemma anyC(h:G.Simple) (x:TwoG G)(i j:Axis): x.val (i,j)=x.val (j,i):=by
     have he(x:TwoG G): splitR acts marks x (i,j)=splitR acts marks x (j,i):= (any_symmetric h (binder (coinR acts marks x))).1 i j
     rw [spun acts marks x (i,j),spun acts marks x (j,i),he,he]
lemma rankRG(h:G.Simple): Module.finrank ℂ (TwoG G)≤4 ∧ Module.finrank ℂ (OneG G)≤3:=by
    haveI: FiniteDimensional ℝ (Label G 4):=Module.Finite.trans ℂ _; haveI : FiniteDimensional ℝ (Label G 5):=Module.Finite.trans ℂ _
    constructor
    · have ht:Injective (binder (G:=G)):=fun x y h=> Subtype.ext (funext fun ⟨a,b⟩=>congr_fun (congr_fun (congr_arg Subtype.val h) a) b)
      exact le_trans (surri acts marks) ((LinearMap.finrank_le_finrank_of_injective ht).trans (finrank_any h))
    have hp:Injective (binderV (G:=G)):=fun x y h=>Subtype.ext (congr_arg (fun x:RawOne G=>x.val) h); exact le_trans (surri Vc sign) ((LinearMap.finrank_le_finrank_of_injective hp).trans (finrank_one h))
end YM.StressFlux.Offer
#print axioms YM.StressFlux.Offer.rankRG
#print axioms YM.StressFlux.Offer.anyC
