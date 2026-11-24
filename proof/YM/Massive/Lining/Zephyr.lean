import YM.Massive.Lining.Temper
/-! # Construct the complete primary stencil symbols.

Single witness, multilinear-algebra and continuity; no cost/IR estimates here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining.Temper
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct ContinuousMap
open Purl Scan Cylinder Paper TensorProduct
variable {H:Source.Hol su}{d h:ℕ}(F:Flag H d h)(U: Kedge H d h)(t:Finset Cover)
local notation "Q" => SpinMode d
local notation "T" => Nearest t 6
local notation "D" => Cylinder.Formula t 6

def porch (x:Land): D →ₗ[ℂ] Dirac T:= (TensorProduct.lid ℂ _).toLinearMap.comp (TensorProduct.map (MvPolynomial.aeval (Source.entry x)).toLinearMap LinearMap.id)
lemma porch_eval (x:Land)(y:D): porch t x y=Cylinder.evaluate x y:=rfl
lemma porch_air (x:Land)(p:Source.Formula su t)(u: Dirac T): porch t x (p ⊗ₜ[ℂ] u) = MvPolynomial.aeval (Source.entry x) p • u:=by rw [porch,LinearMap.comp_apply, TensorProduct.map_tmul,LinearEquiv.coe_coe, TensorProduct.lid_tmul]; rfl
@[fun_prop] lemma porch_c (p:D): Continuous (fun x:Land=> porch t x p):= by
   induction p using TensorProduct.induction_on with
   | zero=> simp_rw [map_zero]; exact continuous_const
   | tmul p u=>
      simp_rw [porch_air]; have ht : Continuous (fun x:Land=> (Source.entry x : Source.Index su t → ℂ)):=by
         apply continuous_pi; rintro ⟨i,a,b,s⟩; unfold Source.entry; split <;> fun_prop
      have he:Continuous (fun x:Land=> MvPolynomial.aeval (Source.entry x) p):= p.continuous_eval.comp ht; exact he.smul continuous_const
   | add p q hp hq=> simp_rw [map_add]; exact hp.add hq
lemma porch_house (x:Land)(p q:D): porch t x (p*q)=porch t x p*porch t x q:=by
   induction p using TensorProduct.induction_on with
   | zero=> simp
   | tmul p u=>
      induction q using TensorProduct.induction_on with
      | zero=>simp
      | tmul q v=> simp_rw [Algebra.TensorProduct.tmul_mul_tmul, porch_air,map_mul]; rw [_root_.smul_mul_assoc,_root_.mul_smul_comm, mul_smul]
      | add q q' h h'=> rw [mul_add,map_add,h,h',map_add,mul_add]
   | add p p' h h'=> rw [add_mul,map_add,h,h',map_add,add_mul]
def Ford (f:Land→Dirac T) := ∃ p:D, (fun x=> porch t x p)=f
namespace Ford
variable {t}
lemma add {f g: Land→Dirac (Nearest t 6)}(hf:Ford t f)(hg:Ford t g): Ford t (fun i=>f i+g i):=by obtain ⟨p,rfl⟩:=hf; obtain ⟨q,rfl⟩:=hg; exact ⟨p+q,funext fun _=> map_add _ _ _⟩
lemma mul {f g: Land→Dirac (Nearest t 6)}(hf:Ford t f)(hg:Ford t g): Ford t (fun i=>f i*g i):=by obtain ⟨p,rfl⟩:=hf; obtain ⟨q,rfl⟩:=hg; exact ⟨p*q,funext fun _=>porch_house ..⟩
lemma fixed (y: Dirac T): Ford t (fun _=>y):=⟨1 ⊗ₜ[ℂ] y,funext fun _=>by rw [porch_air,map_one, one_smul]⟩
lemma plusEP {g:Land→ℂ}(y:Dirac T)(h:Work.G06.EntryPoly t g): Ford t (fun i=> g i • y):=by obtain ⟨p,hp⟩:=h; exact ⟨p ⊗ₜ[ℂ] y,funext fun _=>by rw [porch_air,hp]⟩
lemma EPk {f:Land→Dirac (Nearest t 6)}(hf:Ford t f){g:Land→ℂ}(h: Work.G06.EntryPoly t g): Ford t (fun i=> g i • f i):=by
   have hv(i:Land): g i • f i=(g i • (1:Dirac T))*f i:=by rw [_root_.smul_mul_assoc, one_mul]
   rw [funext hv]; exact (plusEP (1:Dirac T) h).mul hf
lemma seriesL {ι:Type*}(s:Finset ι)(f:ι→ Land→Dirac T)(h:∀ i∈s,Ford t (f i)): Ford t (fun x=>∑ i∈s, f i x):=by
   induction s using Finset.induction_on with
   | empty=> simpa using fixed (0:Dirac T)
   | @insert a s ha ih=> simp_rw [sum_insert ha]; exact (h a (mem_insert_self ..)).add (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma pace (hb: Room F U t)(i:Pairs Q): Ford t (fun x:Land=> ink U t x (atom i)):=by
   let M(x:Land):Matrix Q T ℂ:= start U t x; unfold ink adapter; simp_rw [change_atom]; apply seriesL _ _; intro j _; apply plusEP _; rcases i with i|i <;> rcases j with j|j
   · exact etching F U t hb i j
   · exact EPconst _
   · exact EPconst _
   exact Work.G06.entryPoly_conj (etching F U t hb i j)
lemma sunlight (hb : Room F U t)(y:SpinPol d): Ford t (fun x:Land=> ink U t x y):=by
   induction y using ExteriorAlgebra.induction with
   | algebraMap a=> simp only [AlgHom.commutes]; exact fixed _
   | ι v=> rw [line_atoms]; simp_rw [map_sum,map_smul]; exact seriesL _ _ (fun i _=> (pace F U hb i).EPk (EPconst _))
   | add p q hp hq=> simp_rw [map_add]; exact hp.add hq
   | mul p q hp hq=> simp_rw [map_mul]; exact hp.mul hq
lemma cake (hb: Room F U t)(y:Pol d): Ford t (fun x:Land=>glaze F U t x y):=by
    induction y using TensorProduct.induction_on with
    | zero=>simp_rw [map_zero]; exact fixed _
    | tmul p u=> simp_rw [stencil]; exact (sunlight F U hb u).EPk (brush F U t hb p)
    | add p q hp hq=> simp_rw [map_add]; exact hp.add hq
lemma effect (hb: Room F U t) : ∃ T':Label d→ₗ[ℂ] D,∀ (x:Label d)(u:Land), porch t u (T' x)=glaze F U t u x.val:=by
   haveI:Module.Free ℂ (Label d):=Module.Free.of_divisionRing ℂ (Label d)
   let B:=Module.finBasis ℂ (Label d); choose p hp using fun i=>cake F U hb (B i).val; let T':Label d→ₗ[ℂ] D:= B.constr ℂ p; refine ⟨T',fun x u=>?_⟩; refine DFunLike.congr_fun (f:=(porch t u).comp T') (g:=(glaze F U t u).comp (labels d).subtype) ?_ x; apply B.ext; intro i; change porch t u (T' _)=glaze F U t u (B i).val; rw [show T' (B i)=p i from Module.Basis.constr_basis B ℂ ..]; exact congr_fun (hp i) u
end Ford
namespace Realize
variable {n:Side}
def placeL (b:Cover)(u:Grid n): D→ₗ[ℂ] Fields n 6:= (adapter (Ferry.belt n t b) (Ferry.belt n t b)).toLinearMap.comp (porch t (expandAt (wrap n b) u))
def placed (n:Side)(b:Cover) : D→ₗ[ℂ] Insertion n 6 where
    toFun p:=⟨places b p, (adapter (Ferry.belt n t b) (Ferry.belt n t b)).toLinearMap.continuous_of_finiteDimensional.comp ((porch_c t p).comp (show Continuous (expandAt (wrap n b) (K:=su.El)) from by unfold expandAt; fun_prop))⟩
    map_add' x y:=ContinuousMap.ext (fun u=> map_add (placeL t b u) x y)
    map_smul' c x:=ContinuousMap.ext (fun u=>map_smul (placeL t b u) c x)
lemma location (b: Cover)(p:D)(u:Grid n): placed t n b p u= places b p u:=rfl
end Realize
end YM.Massive.Lining.Temper
#print axioms YM.Massive.Lining.Temper.Ford.effect
