import YM.QCD.Leaf.Bud
import YM.QCD.Orbit.Foil
/-! # preserve reorientation at attenuation: one EXTRA project, not recurrent width
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.LeafM
open Lat Function Lattice Wilson Kit Cost Run Rudder Finset RG Eyrie Stationary Sparks Revolve
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n:Side}{s:Signed}{p:Spike}{g : Site n→ℂ}{k:ℕ}{C : Bloom k}{t ξ:ℝ}

lemma fixedP (W:Slot)(V:Slot) (r:ℝ)(h:Mint s W V r) (x b:Site n)(U: Grid n)(ξ:ℝ): pulp W x ξ (pull s b U)=r • pulp V (affine s b x) ξ U:=by
  have he: W.atSite (pull s b U) x=r • V.atSite U (affine s b x):=by unfold Slot.atSite; rw [expandAt_pull]; exact h.returnF _
  unfold pulp; rw [he,norm_smul,Real.norm_eq_abs,h.price,one_mul,smul_comm]

lemma quest_tag (b : Site n) {r w}(hp : Swing s p)(hg:Glare s 0 0 b g)(h:∀ i,Mint s (C.petals i) (w i) (r i))(U:Grid n):
    trackP (quest C s p w r) ξ n U=aura (star (hues b s g p)) (trackP C ξ n (pull s b U)):=by
  let F:= hues b s g p
  let A:=quest C s p w r
  have he : F* rides (Equiv.refl _) (fun i=> satin A i ξ U)=rides (Equiv.refl _) (fun i=> satin C i ξ (pull s b U))*F:=by
    unfold F hues; rw [ride_mul,ride_mul, Equiv.refl_trans,Equiv.trans_refl]; congr 1; funext i; unfold satin
    have hx j: pulp (C.petals j) i ξ (pull s b U)=r j • pulp (w j) (affine s b i) ξ U:= fixedP _ _ _ (h j) ..
    unfold A; simp only [hx, Matrix.smul_mul,Matrix.mul_smul,Equiv.refl_apply, quest_hues]; -- quest? A
    have hz: star p*p=1:=hp.unit.1
    unfold flag; rw [wave_star]; simp only [← Matrix.mul_assoc, wave_mul]; rw [hz,wave_one,Matrix.one_mul]; rfl -- touches
  have ht:=colour_wheel hg hp
  change rides (Equiv.refl _) (fun i=> satin A i ξ U)*routeM _ _ _= star F * (_*routeM _ _ _) * star (star F)
  rw [star_star, ← Matrix.mul_assoc, hue_path hg hp]
  change _=star F * rides (Equiv.refl _) _*(F*_ *star F)*F; simp only [Matrix.mul_assoc]; rw [show star F*F=1 from ht.1,mul_one,← Matrix.mul_assoc (rides (Equiv.refl _) _) F,← he, Matrix.mul_assoc,← Matrix.mul_assoc (star F), show star F*F=1 from ht.1,one_mul]; rfl

lemma carries (x:Slot) (a:Walk)(U:Grid n)(y:Site n): pulp (roll x a) (stop y a) ξ U=su.adjoint (travel U y a)⁻¹ (pulp x y ξ U):=by unfold pulp; rw [transit,Gauge.norm_adjoint,map_smul]
lemma clover_tag (C:Bloom k)(P:C.Spins)(U:Grid n):
    trackP (clover C) ξ n U=newborn n (trackP C ξ n U):=by
  let w:= C.tail; let h:Equiv.Perm (Site n):=Equiv.addRight (wrap n (stop (0:Cover) w))
  let J:= routeM 0 U w; let R:= fun x => winding x w 0 U
  have hJ: J=rides h R:= pinned ..
  let K:= chirality n; let A:= wave g5
  have hk : star K=K:= chi_star
  have hχ : K=rides (Equiv.refl _) fun _=>A:=rfl
  change rides (Equiv.refl _) _*routeM 0 U (Lattice.reverse w)=K*star (_*J)*star K
  rw [show K*star (_*J)*star K=_ from (rfl), flipping,hk,show routeM 0 U w=J from rfl,hJ,hχ]; simp only [star_mul,yard,ride_ad,ride_mul]; congr 1
  funext i; let y:=h.symm i
  have hh x : h x=stop x w:=(wrap_stop ..).symm
  have hy : i=stop y w:=by rw [← hh,Equiv.apply_symm_apply]
  let B := travel U y w; let V := satin C y ξ U; let T:= touch (colour B)
  have hv: satin (clover C) i ξ U=A*(star T*star V*T)*A:=by
    calc
      _ = flag g5 (star (C.hues fun k=> su.adjoint B⁻¹ (pulp (C.petals k) y ξ U))) := by
        unfold satin; rw [clove]; have hp i (x:Slot): (roll x w).atSite U i= (roll x w).atSite U i:=rfl
        have hm k : pulp ((clover C).petals k) i ξ U=su.adjoint B⁻¹ (pulp (C.petals k) y ξ U):=by rw [show i=stop y w from hy]; exact carries ..
        simp_rw [hm]
      _ = _ := by rw [P]; unfold flag T; simp only [colour_inv,touch_star,star_mul,star_star,wave_star,g5_star, Matrix.mul_assoc]; rfl -- touch_star simp orientation
  rw [show _=_ from hv]; change A*(star T*star V*T)*A*star (shimmer 0 y w • T)=A*(star (shimmer 0 y w • T)*star V)*A
  simp only [star_smul, Matrix.mul_smul,Matrix.smul_mul, Matrix.mul_assoc]; rw [← Matrix.mul_assoc T, show T*A = A*T from (interlace ..).eq,Matrix.mul_assoc A T,show T*star T=1 from (touch_u (x:=colour B) ⟨su.mat_star_mul _,su.mat_mul_star _⟩).2,mul_one]

variable {I J : Type}{Z:I→Bloom k}{V:J→Bloom k}{η b A D r u:ℝ}
def wild (Z:I→Bloom k)(ξ:ℝ) (n:Side)(U:Grid n):Sheet n:=∑' i,trackP (Z i) ξ n U
lemma earns (U:Grid n)(hp: Fractal Z r A)(h:0<ξ)(ht:ξ≤1)(hv:0<r): Summable fun i=> ‖trackP (Z i) ξ n U‖ := by
  obtain ⟨w,c,m,hw,hc,H⟩:=postM k hv (b:=0) le_rfl
  refine ((hp.bills.mul_left c).mul_right (ξ^k)).of_nonneg_of_le (fun _=>norm_nonneg _) fun i=>?_ ; have hi:= (Z i).price_nn.trans ((Z i).paidUp hv.le); exact (H m le_rfl ξ h ht n _ (hp.sect i)).value (by positivity) le_rfl (by positivity) U
lemma orbit (U:Grid n)(hp: Fractal Z r A)(h:0<ξ)(ht:ξ≤1)(hv:0<r): wild (clover∘Z) ξ n U=newborn n (wild Z ξ n U):=by
  unfold wild; have he (i):trackP ((clover∘Z) i) ξ n U=newbornL n (trackP (Z i) ξ n U):= clover_tag _ (hp.sect i) U
  simp only [he]; exact ((newbornL n).map_tsum (earns U hp h ht hv).of_norm).symm
lemma fuse (U:Grid n)(z:ℂ) : wild (fun i=> shape (Z i) z) ξ n U=z • wild Z ξ n U:=by
  have h (W:Bloom k):trackP (shape W z) ξ n U=z • trackP W ξ n U:=by unfold trackP yard; rw [← Matrix.smul_mul,ride_smul]; exact congr_arg (fun v=>rides (Equiv.refl _) v*routeM 0 U W.tail) (funext fun i=> shade_h ..)
  unfold wild; simp_rw [h]; rw [tsum_const_smul'']
lemma tack (U:Grid n)(hp:Fractal Z r A)(h:0<ξ)(ht:ξ≤1)(hv:0<r)(s:Signed): wild (select Z s) ξ n U=inverted (wild Z ξ n) s U:=by
  obtain ⟨L,H⟩:=auraCL (star (scaleA s n)); have hx i: trackP ((select Z s) i) ξ n U=L (trackP (Z i) ξ n (pull s 0 U)):=by
    rw [H]; exact quest_tag 0 (fleetLeft s) (gems s n) (fun j=> (garment ..).choose_spec.choose_spec) U
  unfold wild inverted; simp_rw [hx]; rw [← L.map_tsum (earns _ hp h ht hv).of_norm,H]
lemma raindrop (h : Fractal Z r A)(hq: Fractal V b D) (hp:0<ξ)(ht:ξ ≤1)(hv:0<r)(he:0<b)(U:Grid n): wild (Sum.elim Z V) ξ n U= wild Z ξ n U+wild V ξ n U:= (HasSum.sum (f:=fun i=> trackP (Sum.elim Z V i) ξ n U) (earns U h hp ht hv).of_norm.hasSum (earns U hq hp ht he).of_norm.hasSum).tsum_eq
lemma projected (Z:I→Bloom k)(h: Fractal Z r A)(hp:0<ξ)(ht:ξ ≤1)(hv:0<r): wild (frosting Z) ξ n=occult (hearth (wild Z ξ n)):=by
  have hu : wild (feast Z) ξ n=hearth (wild Z ξ n):=by
    funext U; unfold feast; rw [fuse]; have ht' i: Summable fun j=> trackP (select Z i j) ξ n U:=(earns U (portion h i) hp ht hv).of_norm
    have hx : wild (en Z) ξ n U=∑ i:Signed,inverted (wild Z ξ n) i U:=by
      unfold wild; rw [((earns U (rocky h) hp ht hv).of_norm).tsum_prod,tsum_fintype]; exact sum_congr rfl fun i _=>tack U h hp ht hv i
    rw [hx]; rfl
  funext U; rw [← hu]; unfold frosting frost; rw [fuse]; have hy : 0 < r/(1+k):=by positivity
  rw [raindrop (invested h) (reserves _ hy.le (invested h) (by rw [div_mul_cancel₀ _ (by positivity)])) hp ht hv hy,orbit U (invested h) hp ht hv]; rfl
lemma solidly (Z:I→Bloom k)(h:Fractal Z r A)(hp:0<ξ)(ht:ξ ≤1)(hv:0<r) : Majestic (wild (frosting Z) ξ n):=by rw [projected Z h hp ht hv]; exact ⟨fire_m _ (roaring _),fun x=> (occult_t ..).symm⟩
end YM.QCD.Leaf.LeafM
