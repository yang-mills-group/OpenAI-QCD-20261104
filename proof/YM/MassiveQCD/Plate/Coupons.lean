import YM.MassiveQCD.Plate.Coined
/-! # Exact restoration across every forced mask, over allowed scope -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k B N:ℕ}{s t h a k' σ:ℝ}{J U I E:Type}[Fintype I]
namespace Film
variable (N)(p:I→Site c)(q:I→Bool) (θ:ℝ)(Y:Patron.Rail c N E)(F: Patron.Rail c (ample N I) J) (A:Set (Finset I))
local notation "Z"=> Keys c N -- K not using implicitly
local notation "R"=> Spine I
local notation "mx"=> Keys c N⊕Spine I
local notation "mk"=> Patio mx
local notation "M0"=> Ribbon.ample N I
local notation "off!"=> vacR R Z
local notation "p!"=> rootR R Z
local notation "d!"=> withdraw N p θ
local notation "u!"=> faultK N p θ F
local notation "S!"=> publication N p q F A θ
local notation "St"=> Seats N p F A
variable {X₁ Y₁:Type}[NormedCommRing X₁][NormedAlgebra ℂ X₁][NormedCommRing Y₁][NormedAlgebra ℂ Y₁][FiniteDimensional ℂ X₁][NormOneClass X₁][NormOneClass Y₁][FiniteDimensional ℂ Y₁][CompleteSpace X₁][CompleteSpace Y₁]
omit [Fintype I][NormedAlgebra ℂ X₁][FiniteDimensional ℂ X₁][NormOneClass X₁] in
lemma aloneC (p:I→Hat c)(H:Hat c)(x:I→X₁)(hp:Summable fun i=>‖x i‖): Summable (fun i=> if p i=H then x i else 0):= hp.of_norm.indicator {i| p i=H}
omit [Fintype I][NormedAlgebra ℂ X₁][FiniteDimensional ℂ X₁][NormOneClass X₁] in
lemma coin_merge (p:I→ Hat c)(q:J→ Hat c)(x:I→X₁)(y:J→X₁)(hp:Summable fun i=>‖x i‖)(hy:Summable fun i=>‖y i‖) (u:Hat c): coin (Sum.elim p q) (Sum.elim x y) u= coin p x u+coin q y u:=by
    rw [fingerprint,fingerprint,fingerprint]; let f (i:I⊕J):= if Sum.elim p q i=u then Sum.elim x y i else 0
    exact (HasSum.tsum_eq ((aloneC p u x hp).hasSum.sum (f:=f) (aloneC q u y hy).hasSum)) -- maybe HasSum.sum function explicit
omit [Fintype I] [NormOneClass X₁][NormOneClass Y₁][FiniteDimensional ℂ Y₁][FiniteDimensional ℂ X₁][CompleteSpace Y₁][CompleteSpace X₁] in
lemma payable (φ:X₁→L[ℂ] Y₁){D:I→X₁}(h:Summable fun i=>‖D i‖): Summable (fun i=> ‖ φ (D i)‖):= Summable.of_nonneg_of_le (fun _i=> norm_nonneg _) (fun _i=> φ.le_opNorm _) (h.mul_left _)
omit [Fintype I] [FiniteDimensional ℂ Y₁][NormOneClass Y₁][CompleteSpace Y₁] in
lemma stamps (p:I→Hat c)(X:I→X₁)(W:Support c)(u:X₁→ₐ[ℂ]Y₁)(h:Summable fun i=> ‖X i‖): u (∑' i,Plate.roof p X W i)=∑' i,Plate.roof p (u ∘ X) W i:=Eq.trans (u.toLinearMap.toContinuousLinearMap.map_tsum (rum p X W h)) (tsum_congr fun i=>by unfold Plate.roof; split; exact map_prod u ..; exact map_zero _)
-- Restoration theorem uses Ω.Rise equality on unmarked per-Hat status AFTER comparing publications. Can derive later with altitude s.Projections. 
variable (M:Finset I) -- shadows M! avoid
variable (hp:(M.powerset:Set (Finset I))⊆ A) (hV:∀ i U,Well N p θ q (F.warp i U)) (hr:0<θ) (hf:F.Reg t)
variable (hc:Correspond (faultK N p θ F) Y)(U:Grid c) -- ref uses.R mask.Y can separate by ext.B.
variable (hU:Summable fun i=> ‖F.warp i U‖)
local notation "op"=> shutter Z M
include hU hV hr hf hp
lemma coin_off (H: Hat c): op (d! (coin F.addr (fun i=> F.warp i U) H))= op ( p! (coin (F.addr) (fun i=> (u!).warp i U) H) + coin (S!).addr (fun i=> (S!).mark i U) H):=by
     let L x:= F.warp x U; let X' i:= (off!) (d! (L i))
     let v (i:St):= (S!).mark i U; let O:= (op).comp d!; let PS:= (op).comp p!
     have hΩ:= (payable ((PS.comp ((off!).comp d!)).toLinearMap.toContinuousLinearMap) hU); let vf v:= op v
     rw [map_add]; change op (d! (coin F.addr L H))= op (p! (coin F.addr X' H))+ op (coin (S!).addr v H); rw [show op (p! (coin _ _ _))= _ from (readycoin (F.addr) X' H PS.toLinearMap.toContinuousLinearMap (payable (((off!).comp d!)).toLinearMap.toContinuousLinearMap hU)).symm, show op (coin _ _ _)= _ from (readycoin (S!).addr v H (op).toLinearMap.toContinuousLinearMap (seat_norm N p q θ F A U hU)).symm, show op (d! (coin _ _ _))= _ from (readycoin F.addr L H O.toLinearMap.toContinuousLinearMap hU).symm]
     let f i:= if F.addr i=H then vf (d! (L i)) else 0; let g i:= if F.addr i=H then PS (X' i) else 0; let r(i:St):= if (S!).addr i=H then vf (v i) else 0; let h (i:J):=∑' j,r (⟨i,j⟩:St); rw [fingerprint,fingerprint,fingerprint]; change (∑' i,f i)=(∑' i, g i)+∑' i,r i
     have h₁:Summable g:= aloneC F.addr H _ hΩ; have h₂:Summable r:=somG (p:=(S!).addr) (payable (op).toLinearMap.toContinuousLinearMap (seat_norm N p q θ F A U hU)) H
     have h₃: Summable h:= h₂.sigma -- edit
     rw [h₂.tsum_sigma, ← h₁.tsum_add h₃]; refine tsum_congr fun i=>?_; change f i = g i + h i; unfold h; rw [tsum_fintype]; unfold f g r; split
     next he=> change vf (d! _) = _ + ∑ j:↥(seats p A (F.addr i)),_; simp_rw [show ∀ j:↥(seats p A (F.addr i)), (S!).addr (⟨i,j⟩:St)= H from fun _=> he, if_true]; unfold vf; rw [← map_sum]; exact (roofOut N p q θ F A i U M hp hf (hV i U) hr).trans (map_add (op) ..)
     next he => rw [zero_add]; apply Eq.symm; refine sum_eq_zero (fun j _ => if_neg (fun hv=>he hv)) -- if_pos rhs? check
include hc
lemma mergeFront : shutter Z M (Film.reports N S! Y t U) = testifyK N p θ F U M (t:=t):=by
    let D:= RG.flags t U; let v (i:E⊕St):= spruced N S! Y i U; let f:=addressSets N S! Y; let g i:= F.warp i U; let L:= (op).comp d!; have hm : Summable (fun i=>‖v i‖) := Summable.sum _ (payable (p!).toLinearMap.toContinuousLinearMap (hc.coins U)) (seat_norm N p q θ F A U hU)
    change op (∑' i,Plate.roof f v D i)= L (∑' i,tK F t U i); simp_rw [termsK]; rw [stamps f v _ _ hm,stamps _ _ _ L hU]; apply Eq.trans (catalogue _ _ _ (payable (op).toLinearMap.toContinuousLinearMap hm)); refine Eq.trans ?_ (catalogue F.addr _ _ (payable L.toLinearMap.toContinuousLinearMap hU)).symm; apply congr_arg (fun (d:Hat c→mk)=> ∑' i, Plate.roof id d D i); funext T; have hqq:= hc.governs T U
    have he:= readycoin f v T (op).toLinearMap.toContinuousLinearMap hm; apply Eq.trans he; rw [show coin f v T= _ from coin_merge Y.addr (S!).addr (p! ∘ (fun i=> Y.warp i U)) (fun i=>(S!).mark i U) (payable (p!).toLinearMap.toContinuousLinearMap (hc.coins U)) (seat_norm N p q θ F A U hU) T, show coin Y.addr (p! ∘ _) T= p! (coin _ _ _) from readycoin Y.addr (fun i=>Y.warp i U) T (p!).toLinearMap.toContinuousLinearMap (hc.coins U),← hqq] -- implicit f composition pruced not defeq? need congr
    exact ((coin_off N p q θ F A M hp hV hr hf U hU T).symm).trans (readycoin F.addr _ T L.toLinearMap.toContinuousLinearMap hU).symm -- hp shadow.B
end Film
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Film.mergeFront
