import YM.QCD.Pearl.Bridge

/-!
# Fourier convention for charge-carrying sheets
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lattice Wilson Function Finset Metric Lat Rudder Kit RG
open Laurent Bloch Flume Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Kronecker Topology
variable {n : Side} (C : su.Color)
def flash (p:Momentum)(i: Axis):Edge Cover→ℂ:=fun x=> if i=x.2 then mode p x.1 else 0
def flashT (p:Site n)(i:Axis):Weather n:=fun x=>if i=x.2 then cell p x.1 else 0

def cloud (p:Site n)(V: Site n→Bundle):Sheet n:= rides (Equiv.addRight (-p)) fun i=> V (i-p)
lemma cloudy (p:Site n) (X : Bundle): peel (rides (Equiv.refl _) (fun i : Site n=> cell p i • X))= cloud p fun _=> X:=by
  apply peel_eq; ext ⟨i,x⟩ ⟨j,y⟩
  have he k : k -p=j ↔ k=j+p:=by rw [sub_eq_iff_eq_add]
  have hx : (Equiv.addRight (-p)).toFun=fun k : Site n=>k-p :=by ext; simp[sub_eq_add_neg,Equiv.addRight]
  have hk : cell p i*scarf j i=scarf (j+p) i:=by rw [scarf,scarf,cell_duality (j+p) i,cell_add,cell_duality j i,cell_duality p i]; ring
  rw [Matrix.mul_apply,Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type,sum_eq_single i,sum_eq_single (j+p)]
  · simp only [rr,Equiv.refl_apply,if_true,Matrix.smul_apply,leaf, Matrix.kronecker_apply,Matrix.one_apply,plain,Matrix.of_apply,smul_eq_mul, cloud];
    change (∑ a:Fiber, _)=∑ a:Fiber, scarf (j+p) i*_*(if (Equiv.addRight (-p)).toFun (j+p)=j then _ else _);
    rw [hx]; simp only [add_sub_cancel_right,if_true]; simp_rw [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,sum_ite_eq,sum_ite_eq',mem_univ, if_true, ← hk]; ring
  · intro k _ h; refine sum_eq_zero fun y _=>?_ ; unfold cloud; rw [rr,if_neg,mul_zero]; exact fun hh=> h ((he k).mp (by rw [sub_eq_add_neg]; exact hh))
  · simp
  · intro k _ h; simp [rr,Ne.symm h]
  simp
lemma cloud_side (p:Site n)(X Y:Site n→Bundle): cloud p X * lined Y=cloud p (X*Y):=by
  unfold cloud lined; rw [ride_mul]; congr 1; funext i; simp [Equiv.addRight,sub_eq_add_neg]
lemma side_cloud (p:Site n)(X Y:Site n→Bundle): lined X * cloud p Y= cloud p fun i=> X (i+p)*Y i:=by
  unfold cloud lined; rw [ride_mul]; congr 1; funext i; simp
lemma cloud_dawn (p:Site n)(X Y:Site n→Bundle): cloud (-p) X*cloud p Y=lined fun i=> X (i+p)*Y i:=by
  unfold cloud lined; rw [ride_mul]; simp only [neg_neg]; congr 1
  · ext1 i; simp [Equiv.addRight]
  funext i; simp [Equiv.addRight]
lemma line_clear (M: Bundle) : peel (rides (Equiv.refl _) (fun _ : Site n=>M))= lined fun _=>M:=by
  have hp:= cloudy (0:Site n) M; simp_rw [fun i=> cell_duality (0:Site n) i, cell_origin,one_smul] at hp; rw [hp]; unfold cloud lined; congr 1; ext1 i; simp [Equiv.addRight]
lemma rumble (p:Site n)(x:Cover) : mode (-mon p) x=cell (-p) (wrap n x):=by rw [mode_inverse,← cell_wrap,cell_duality (-p),cell_inverse, cell_duality p]
lemma banner {p: Momentum}{P:Site n} (h : ∀ x:Cover, mode p x = cell P (wrap n x)) (a:Axis)(x:Site n)(y:Cover)(w:Walk):
    bill (flashT P a) (x+ wrap n y) w=cell P x * bill (flash p a) y w:=by
  induction w generalizing y with
  | nil=> simp[bill]
  | cons i w ih=>
    rw [bill,bill,mul_add]; congr 1
    · have he (u : Cover): flashT P a (x+wrap n u,i.dir)= cell P x * flash p a (u,i.dir):= by
        dsimp only [flashT,flash]; split
        · rw [cell_add,h]
        rw [mul_zero]
      cases hv:i.neg <;> simp only [hv,Bool.false_eq_true,↓reduceIte,Step.used,mul_neg]
      · exact he y
      rw [← he,map_sub, wrap_step,add_sub] -- inspect
    rw [add_assoc, ← wrap_vec n i, ← map_add, ih]

def glitter (w:Walk)(p:Momentum)(i:Axis):=bill (flash p i) (0:Cover) w
def hack (S:Slot)(p:Momentum)(i:Axis):=bill (flash p i) S.offset (Lattice.square S.plaq.val.1 S.plaq.val.2)
lemma rosen {p:Momentum}{P:Site n} (h : ∀ x:Cover,mode p x= cell P (wrap n x))(i : Axis)(S:Slot)(x : Site n):
    tick S x (flashT P i)=cell P x*hack S p i:=by unfold tick; rw [add_comm,banner h]; rfl
lemma billow {p:Momentum}{P:Site n} (h : ∀ x:Cover,mode p x=cell P (wrap n x))(i:Axis)(w:Walk)(x:Site n):
    bill (flashT P i) x w=cell P x* glitter w p i:=by simpa only [glitter,map_zero,add_zero] using banner h i x 0 w
lemma mirrorAm (w:Walk)(p:Site n)(i:Axis):dew (flashT p i) (amass C 0 w) 0=rides (Equiv.refl _) (fun x:Site n=> cell p x • (glitter w (mon p) i • touch (echo C)))*routeM 0 1 w:=by rw [amass_dew,pump]; simp_rw [billow (p:=mon p) (fun x=>(cell_wrap ..).symm), smul_smul]
lemma bodyAm (w:Walk)(p:Site n)(i:Axis):dig (flashT p i) (flashT (-p) i) (amass C 0 w) 0=rides (Equiv.refl _) (fun _ : Site n=> (glitter w (-mon p) i*glitter w (mon p) i) • touch (echo C*echo C))*routeM 0 1 w:=by
  rw [amass_dig]; congr 1; congr 1; funext x; congr 1; rw [billow (p:=mon p) (fun x=>(cell_wrap ..).symm),billow (fun x=>rumble p x),cell_duality (-p) x,cell_inverse, ← cell_duality p x, mul_mul_mul_comm,inv_mul_cancel₀ (cell_ne p x),one_mul]
end YM.QCD.Pearl
