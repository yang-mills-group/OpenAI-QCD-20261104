import YM.QCD.Runnel.Lobe

/-! # concrete Sample witnesses, notch compression -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {s f : Side} (t : Site f) {δ b c C : ℝ} {n r B p j k : ℕ} (P : Plan j) (v : Train j)

structure Quota (P : Plan j) (δ b c C : ℝ) (n : ℕ) : Prop where
 hb : 0≤b
 hd : 0<δ
 hc : 0<c
 hr : 0<n
 hg : Pile b (2*n)*gal δ^n≤ Real.exp (c*n)
 ha (v : Train j) (a) : Laurent.Width (2*c) C (alphaT v a)
 hv (v : Train j) (a): Laurent.Width (2*c) C (P.Herm v a)
lemma quantified (b : ℝ) (hb : 0≤b):∃ c C n δ,Quota P δ b c C n:=by
  obtain ⟨a,A,ha,hA,H⟩:= alpha_cash P.good (fun i:Train j=>i);
  obtain ⟨z,Z,hz,hZ,T⟩:= P.herm_paid (fun i:Train j×Axis=> i.1) (fun i=>i.2)
  let c:=min a z/2; have hc:0<c:=div_pos (lt_min ha hz) (by norm_num)
  obtain ⟨n,δ,hn,hd,h⟩:=ballad b hc
  refine ⟨c,max A Z,n,δ,hb,hd,hc,hn,h,fun v i=> (H i v).mono (by dsimp[c]; linarith [min_le_left a z]) (le_max_left ..),fun v i=>(T (v,i)).mono (by dsimp[c]; linarith [min_le_right a z]) (by simpa using le_max_right A Z)⟩
variable (hq : Quota P δ b c C n) (hB : 2*n≤B)
include hq hB

def alphaV (a : Axis)(p : ℕ) : St f := fun U=> onSpin f (gamma a)*deck t U (corto (alphaT v a) p)
lemma shootZ (a : Axis): Sample δ b c B (fun U=> arcL t U a) (fun U=> arcL t U a) (Real.exp b+Real.exp (c*n)* Real.exp c) p 2:=by
  have he:=Pride.trail t [posDir a] hq.hb hq.hd hq.hc hq.hr hB hq.hg
  have hh:(fun U=>routeM t U [posDir a])=(fun U=>shift t U a):=by simp [routeM,leg,posDir]
  rw [hh] at he; simp only [List.length_singleton, Nat.cast_one, mul_one] at he
  refine Sample.exact_X ((Pride.stiff hq.hb).minus he) ?_ (by positivity)
  exact Reads.single.minus ((shifting t a).dilate (by decide))
lemma shootA (a : Axis): Sample δ b c B (fun U=>vein t v a U) (alphaV t v a p) (2*Pile b 0*(C*Real.exp (c*n))) p (2*p):=by
  have hp := pupil (f:=f) (gamma a)
  let Z : St f:= fun _=> onSpin f (gamma a)
  have he : Sample δ b c B Z Z (Pile b 0) p 0:=by
    refine Sample.exact_X ?_ hp (pile_pos ..).le
    have hg (k:Frame f): Z (gauge k 1)=circulant id k*onSpin f (gamma a)*star (circulant id k):=by
      change onSpin _ _ = siteRot k* _ *star (siteRot k); rw [(rot_spin ..).eq, Matrix.mul_assoc,(siteRot_u k).2,mul_one] -- check
    have hh : Own f δ b B Z (Pile b 0):=by
      rw [← mul_one (Pile b 0)]; exact tiled injective_id injective_id hq.hb (Nat.zero_le B) zero_le_one (fun _ : Pulse f=>Z 1) (fun _=>rfl) hp (fun i k=>hg k) (fun _ _=> differentiableAt_const _) (fun _ _=> gammaQ a)
    refine ⟨hh,?_⟩; rw [show star Z=Z from funext fun i=> by unfold Z; simp [on_spin_star]]; exact hh
  have ht:= he.bond (supplyDeck t _ (hq.ha v a) hq.hb hq.hd hq.hc hq.hr hB hq.hg (p:=p)) hq.hd hq.hb
  rw [zero_add] at ht; exact ht.mono (by linarith) le_rfl -- defeq

def pads (a : Axis) (p:ℕ) : St f:= fun U=>
  let Z := arcL t U a; let F:=deck t U (corto (P.Herm v a) p)
  (P.μ:ℂ) • leaves Z + half (leaves (F*Z)) (leaves (F*star Z))
def price_pad (j i k : ℝ) := (j*(2*k*k) + (1/2)*(2*(2*i*k)^2+2*(2*i*k)^2))
lemma pad (a : Axis): Sample δ b c B (fun U=>walls P t v U a) (pads t P v a p) (price_pad P.μ (C*Real.exp (c*n)) (Real.exp b+Real.exp (c*n)* Real.exp c)) p (6*p+12):=by
  have hr:=shootZ (p:=p) t P hq hB a; have hs:=supplyDeck (p:=p) t _ (hq.hv v a) hq.hb hq.hd hq.hc hq.hr hB hq.hg
  have he (X Y:St f) {R:ℝ} {w:ℕ} (h : Sample δ b c B X Y R p w):Sample δ b c B (star X*X) (star Y*Y) (2*R^2) p (3*w):=(h.adj.bond h hq.hd hq.hb).mono (le_of_eq (by ring)) (by omega)
  have hy:= he _ _ hr; have hh := he _ _ (hs.bond hr hq.hd hq.hb); have ht:= he _ _ (hs.bond hr.adj hq.hd hq.hb)
  let m:= 6*p+12
  have hx:= ((hy.mono (n:=6*p+12) le_rfl (by omega)).scalar (P.μ:ℂ)).both (((hh.mono (n:=6*p+12) le_rfl (by omega)).both (ht.mono (n:=6*p+12) le_rfl (by omega))).scalar (2:ℂ)⁻¹)
  exact hx.mono (le_of_eq (by unfold price_pad; norm_num [abs_of_nonneg P.price.le,Real.norm_eq_abs]; ring)) le_rfl

def padage (P : Plan j) (b c C:ℝ) (n : ℕ):= price_pad P.μ (C*Real.exp (c*n)) (Real.exp b+Real.exp (c*n)* Real.exp c) + 2*Pile b 0*(C*Real.exp (c*n))
omit hq hB in
lemma const_pos (hq : Quota P δ b c C n): 0≤C:=by have h:= hq.ha (.top j) 0; exact (tsum_nonneg h.1).trans h.2.2
lemma stroller : ∃ Z : St f,Sample δ b c B (wood P t v) Z (4*padage P b c C n) p (6*p+12):=by
  let M (i : Axis) : St f := fun U=> walls P t v U i+skewL (vein t v i U); let V (i:Axis) : St f:= fun U=> pads t P v i p U+skewL (alphaV t v i p U)
  have h (i:Axis) : Sample δ b c B (M i) (V i) (padage P b c C n) p (6*p+12):=by
    have hh:=shootA t P v hq hB (p:=p) i
    have ht:= pad t P v hq hB (p:=p) i
    have he := ht.both (((hh.mono (n:=6*p+12) le_rfl (by omega)).apart (hh.adj.mono (n:=6*p+12) le_rfl (by omega))).scalar (2:ℂ)⁻¹)
    exact he.mono (le_of_eq (by unfold padage; norm_num; ring)) le_rfl
  refine ⟨∑ i,V i,?_⟩; rw [show wood P t v=∑ i,M i from funext fun i=> by rw [Finset.sum_apply]; rfl, show 4*padage P b c C n=∑ _ : Axis, padage P b c C n by simp [Axis]]; exact Sample.group _ fun i _=> h i
lemma notched (F : Flight j k) (h : f.val=s.val*F.L.val) (w : ℝ) (hw : 0<w):∃ Z : St f,
  Sample δ b c B (fun U => notch w (vaultF P F h t U)) Z (Real.exp b+w*(4*padage P b c C n+tubeY F.L b c j n ^ 2)) p (6*p+12+6*arctic F.L j):=by
  obtain ⟨Z,hZ⟩:= stroller t P F.wing hq hB (p:=p)
  let S:= 6*p+12+6*arctic F.L j
  have hq' := roomQ (p:=p) F h t hq.hb hq.hd hq.hc hq.hr hB hq.hg
  have ht := (Sample.one hq.hb).apart (((hZ.mono le_rfl (Nat.le_add_right _ (6*arctic F.L j))).both (hq'.mono le_rfl (show 6*arctic F.L j≤ S from by unfold S; omega))).scalar (w:ℂ))
  rw [Complex.norm_real,Real.norm_of_nonneg hw.le] at ht; exact ⟨_,ht⟩
end YM.QCD.Run
