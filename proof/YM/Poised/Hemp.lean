import YM.Poised.Jade
import YM.Poised.Intone
/-!
# Spin jars.
Actual cost relative scales and anchor shift. Absorb displacement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre Place Lining Lining.Ferry QCD.Brick
open YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run Laurent Newt
variable (P:Flight n m)(D:l.val=c.val * P.L.val)
variable (b:Cover) [Fintype B]
abbrev beamW (w:B→ℝ) : (B→ ℂ) →L[ℝ] Alg B:= LinearMap.toContinuousLinearMap {
   toFun x:=∑ i:B,(w i:ℂ) • (x i • atom i),map_add':=fun x y=>by simp only [Pi.add_apply,add_smul,smul_add,sum_add_distrib],map_smul':=fun r x=>by rw [Finset.smul_sum]; refine sum_congr rfl fun i _=> ?_; change _ • ((r • x i) • atom i)=_ ; change _ = r • ((w i:ℂ) • (x i • atom i)); rw [smul_comm r,smul_assoc] }
set_option maxHeartbeats 570000 in
lemma beam_price (w:B→ℝ)(hw:∀ i,0 ≤ w i)(x:B→ℂ): ‖beamW w x‖=capW w x:=by
    let q(i:B):= ‖(w i:ℂ)*x i‖; have he(i):q i=w i*‖x i‖:=by unfold q; rw [norm_mul,Complex.norm_real, Real.norm_of_nonneg (hw i)]
    rw [norm_def,capW]; simp_rw [← he]; classical
    let e:B ↪ Finset B := ⟨fun i=>{i}, Finset.singleton_injective⟩; let f:=beamW w x; symm
    calc ∑ i,q i=∑ i,‖coef (e i) f‖:= sum_congr rfl fun i _=>by
            change _= ‖coef {i} (∑ j,(w j:ℂ) • (x j • atom j))‖; rw [map_sum,Finset.sum_eq_single i]
            · rw [map_smul,map_smul,←mono_single,Grass.read,smul_eq_mul,smul_eq_mul,mul_one]
            · intro j _ hj; rw [map_smul,map_smul,←mono_single, read_other _ _ (show ({i}:Finset B)≠ {j} from e.injective.ne hj.symm),smul_zero,smul_zero]
            simp
         _=∑ i∈Finset.univ.map e,‖coef i f‖:=(Finset.sum_map univ e (fun i=> ‖coef i f‖)).symm
         _=∑ i,‖coef i f‖:= Finset.sum_subset (Finset.subset_univ _) (fun i _ h=>by
             change ‖coef i (∑ j,(w j:ℂ) • (x j • atom j))‖ =0; rw [map_sum,sum_eq_zero,norm_zero]; intro j _; rw [map_smul,map_smul,←mono_single, read_other i _ (show i ≠ {j} from show i≠e j from fun he=> h (he.symm ▸ mem_map_of_mem e (mem_univ j))),smul_zero,smul_zero])
section Linear
variable [NormedAddCommGroup A][NormedSpace ℝ A][NormedAddCommGroup E][NormedSpace ℝ E](L:A→L[ℝ] E)(F:Cover→A)
lemma go (i:Axis): L ∘ Newt.jump F i=Newt.jump (L ∘ F) i:=funext fun _=> map_sub ..
lemma iter (t:List Axis): L∘Newt.iterate F t=Newt.iterate (L∘F) t:=by
   induction t generalizing F with
   | nil=>rfl
   | cons i t ih=>rw [Newt.iterate,ih,go,Newt.iterate]
lemma patch (k:ℕ): L∘piece k F =piece k (L ∘ F):=by
   induction k generalizing F with
   | zero=>rfl
   | succ k ih=> funext x; change L (piece (k+1) F x)=_; rw [piece,piece,map_smul,map_sum]; apply congr_arg; refine sum_congr rfl fun i _=>?_ ; rw [map_smul]; refine congr_arg _ ?_; have h:= ih (Newt.jump F i); rw [go] at h; exact congr_fun h _
lemma pin (k:ℕ): L∘Newt.tail k F= Newt.tail k (L∘F):= funext fun x=>by
   unfold Newt.tail Function.comp -- name
   rw [map_sub]; apply congr_arg; unfold Newt.take; rw [map_sum]; exact Finset.sum_congr rfl fun j _=> congr_fun (patch L F j) _
end Linear
def symbols (f:Cover → Flet B)(u:Fin (d+1))(x : Cover): Flet B:= if u.val<d then piece u.val f (vector x) else Newt.tail d f x
private lemma habit (W:VectorD (Site l) B)(x: Site l): asks W x=frond b x • rowsA b W (Beacon.offset b x):=by
   unfold rowsA frond Beacon.offset; rw [map_add, wrap_lift,sub_add_cancel,smul_smul,ap_sq,one_smul]
private lemma crystalsH (f:Cover→ Flet B)(d:ℕ)(x:Cover): ∑ i:Fin (d+1),symbols f i x=f x:=by
    rw [Fin.sum_univ_castSucc]; simp only [symbols,Fin.val_last,Fin.val_castSucc,lt_self_iff_false, ↓reduceIte]; have he:(∑ i:Fin d,if i.val<d then piece i.val f (vector x) else tail d f x)= Newt.take d f x:=by simp only [Fin.is_lt,if_true]; rw [Fin.sum_univ_eq_sum_range (fun i=> piece i f (vector x)) d]; rfl
    rw [he, Newt.tail,add_sub_cancel]
def pathV (v:VectorD (Site l) B)(t:Fin (d+1)): VectorD (Site l) B:= flats fun x=>frond b x • symbols (rowsA b v) t (Beacon.offset b x)
lemma pathV_pay (v:VectorD (Site l) B)(d:ℕ): ∑ i:Fin (d+1), pathV b v i=v:=by
   apply flat_ext; intro k; change askCL k (∑ i:Fin (d+1), pathV b v i)=asks v k
   rw [map_sum]; have hp(i:Fin (d+1)) : askCL k (pathV b v i)=frond b k • symbols (rowsA b v) i (Beacon.offset b k):= by change asks (pathV b v i) k = _; unfold pathV; rw [invers] -- inspect
   simp_rw [hp,← Finset.smul_sum,crystalsH,← habit]
lemma inR_bu (v:VectorD (Site l) B)(i:Fin (d+1))(V:Support l)(h:i.val<d): Buoyant (0,pathV b v i) V b (3+2*i.val):=by
   refine ⟨(Buoyant.inertV (B:=B) V b).1,piece i.val (rowsA b v),?_,fun x hx=>?_⟩
   · rw [show (3+2*i.val-1)/2=i.val+1 by omega]; exact charged _ (Newt.housed (rowsA b v) i.val)
   change asks (pathV b v i) x=_; unfold pathV; rw [invers]; rw [symbols,if_pos h]
end Pipes
end YM.Massive.Poised
