import YM.QCD.Runnel.Cinch

/-! # interpolation grid leg (both edges) -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {c f : Side} (r : Ratio c f) {δ b ε C : ℝ} {n p B j k : ℕ}
def Wing (M : Grid f→Rail c f) (δ b : ℝ) (B : ℕ) (C : ℝ): Prop := Heritage r.embed id δ b B M C ∧ Heritage id r.embed δ b B (fun U=> (M U)ᴴ) C
lemma rootOwn (hb : 0≤b): Wing r (fun _=>scoop r) δ b B (Pile b 0):=by
  have hg (k:Frame f) : scoop r=siteRot (k∘r.embed)*scoop r*star (siteRot k):=by
    rw [← show scoop r*siteRot k=siteRot (k∘r.embed)*scoop r from roots ..,Matrix.mul_assoc,(siteRot_u k).2,Matrix.mul_one] -- check syntax
  have hp (k:Frame f) : (scoop r)ᴴ=siteRot k*(scoop r)ᴴ*star (siteRot (k∘r.embed)):=by
    have hh:=congr_arg Matrix.conjTranspose (hg k); rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,← Matrix.star_eq_conjTranspose (star _),star_star,← Matrix.mul_assoc] at hh; exact hh
  constructor
  · rw [← mul_one (Pile b 0)]; exact tiled r.embed_injective injective_id hb (Nat.zero_le B) zero_le_one (fun _ : Pulse f=> scoop r) (fun _=>rfl) (scooping r) (fun i k=>hg k) (fun _ _=>differentiableAt_const _) (fun _ _=> (price_scoop r).le)
  rw [← mul_one (Pile b 0)]; exact tiled injective_id r.embed_injective hb (Nat.zero_le B) zero_le_one (fun _ : Pulse f=>(scoop r)ᴴ) (fun _=>rfl) (scooping r).turn (fun i k=>hp k) (fun _ _=>differentiableAt_const _) (fun _ _=> (Matrix.l2_opNorm_conjTranspose (scoop r)).le.trans (price_scoop r).le)
namespace Wing
variable {r} {M : Grid f→Rail c f} {I : Type*} [Fintype I]
lemma mono {p:ℝ} (h : Wing r M δ b B C) (he : C≤p): Wing r M δ b B p:=⟨h.1.mono he,h.2.mono he⟩
lemma scalar (t : ℂ) (h : Wing r M δ b B C): Wing r (fun i=> t • M i) δ b B (‖t‖*C):= by
  refine ⟨h.1.scalar ..,?_⟩
  simp_rw [Matrix.conjTranspose_smul]; simpa only [norm_star] using! h.2.scalar (star t) -- !
lemma group (M : I→Grid f→Rail c f) (Q : I→ℝ) (h : ∀ i, Wing r (M i) δ b B (Q i)): Wing r (fun U=>∑ i,M i U) δ b B (∑ i,Q i):= by
  refine ⟨Heritage.joined _ _ (fun i _ => (h i).1),?_⟩; simp_rw [Matrix.conjTranspose_sum]; exact Heritage.joined _ _ fun i _=> (h i).2
lemma stern {W : St f} {p : ℝ} (h : Wing r M δ b B C) (e : Pride δ b B W p) (hd : 0<δ) (hb : 0≤b) (ht : 0≤C) (hp : 0≤p): Wing r (fun i=>M i*W i) δ b B (C*p):=by
  refine ⟨h.1.meet e.1 hd hb ht hp,?_⟩; simp_rw [Matrix.conjTranspose_mul]; rw [mul_comm]; exact e.2.meet h.2 hd hb hp ht
end Wing
variable (F : Flight j k) (h : f.val=c.val*F.L.val)

def sock (L : Side) (b ε:ℝ) (j n : ℕ):=Pile b 0*(Real.exp (ε*n)*Real.exp (ε*arctic L j))
def tubeY (L : Side) (b ε:ℝ) (j n : ℕ):= massL L*sock L b ε j n
lemma sock_pos (L : Side) (b ε:ℝ) (j n : ℕ): 0<sock L b ε j n:= mul_pos (pile_pos ..) (by positivity)
lemma tubeY_pos (L : Side) (b ε:ℝ) (j n : ℕ): 0<tubeY L b ε j n:= mul_pos (mass_pos _) (sock_pos ..)
lemma line_grit (t : Site f) (o : Lattice.Order) (hb : 0≤b) (hd : 0<δ) (hc : 0<ε) (hr : 0<n) (ht : 2*n≤B) (hg : Pile b (2*n)*gal δ^n≤ Real.exp (ε*n)): Wing (sliceL F h) (fun U=>lineF F h t U o) δ b B (sock F.L b ε j n):=by
  let M (p:F.patch.Points) (U:Grid f):=scoop (sliceL F h)* routeM t U (route 0 p.val o)
  let V:=sock F.L b ε j n
  have he p: Wing (sliceL F h) (M p) δ b B V:=by
    have hP := Pride.trail t (route 0 p.val o) hb hd hc hr ht hg; apply Wing.stern (rootOwn (sliceL F h) hb) (hP.mono ?_) hd hb (pile_pos ..).le (by positivity)
    gcongr; exact stems ..
  have hw p: ‖(F.patch.weight p:ℂ)‖= F.patch.weight p:=by rw [Complex.norm_real, Real.norm_of_nonneg (F.patch.weight_nonneg _)]
  have hh:=Wing.group _ _ (fun i=> (he i).scalar (F.patch.weight i:ℂ)); simp_rw [hw, ← sum_mul,F.patch.weight_sum,one_mul] at hh; exact hh
lemma rectify (t : Site f) (hb : 0≤b) (hd : 0<δ) (hc : 0<ε) (hr : 0<n) (ht : 2*n≤B) (hg : Pile b (2*n)*gal δ^n≤ Real.exp (ε*n)): Wing (sliceL F h) (tied F h t) δ b B (tubeY F.L b ε j n):=by
  have hh:=((Wing.group _ _ (fun o=> line_grit F h t o hb hd hc hr ht hg)).scalar (votes:ℂ)⁻¹).scalar (massL F.L:ℂ)
  rw [norm_inv,Complex.norm_natCast,Complex.norm_real,Real.norm_of_nonneg (mass_pos _).le, sum_const,card_univ,nsmul_eq_mul,← mul_assoc (votes:ℝ)⁻¹,inv_mul_cancel₀ poll_pos.ne',one_mul] at hh; exact hh
lemma tieReads (t : Site f): Reads (perch (sliceL F h)) eye (2*arctic F.L j) (tied F h t):=by
  unfold tied lineF; refine Reads.coin (Reads.coin (Reads.collect fun o => Reads.collect (fun i=> Reads.coin ?_ _)) _) _
  exact (((scooping _).across (membership t _))).dilate (by rw [zero_add]; gcongr; exact stems ..)
lemma roomQ (t : Site f) (hb : 0≤b) (hd : 0<δ) (hc : 0<ε) (hr : 0<n) (ht : 2*n≤B) (hg : Pile b (2*n)*gal δ^n≤ Real.exp (ε*n)): Sample δ b ε B (fun U=> (tied F h t U)ᴴ*tied F h t U) (fun U=> (tied F h t U)ᴴ*tied F h t U) (tubeY F.L b ε j n ^ 2) p (6*arctic F.L j):=by
  have hp := rectify F h t hb hd hc hr ht hg; have he := tieReads F h t; have hh:=(tubeY_pos F.L b ε j n).le
  refine Sample.exact_X ?_ ((he.turn.across he).dilate (by omega)) (by positivity)
  have H := hp.2.meet hp.1 hd hb hh hh
  rw [pow_two]; constructor
  · exact H
  rw [show star (fun U=>(tied F h t U)ᴴ*tied F h t U)= (fun U=>(tied F h t U)ᴴ*tied F h t U) from funext fun U=> by simp [Matrix.star_eq_conjTranspose]]; exact H
end YM.QCD.Run
