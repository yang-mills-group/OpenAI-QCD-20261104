import YM.QCD.Runnel.Crunch

/-!
# reference book: high inverse, core log traced later, attached Schur. All axes. All U.
Constants tolerance after step choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {s f L : Side} {M X : St f} {δ b c g q ε R D u : ℝ} {B v n p j k : ℕ}
lemma c_n (hu : Own f δ b B M R) (hq : Own f δ b B (M^v) (1/2)) (hp : 0<v) (hv : 1≤R)
    (hd : 0<δ) (hb : 0≤b) (n : ℕ): Own f δ b B (M^n) (((1/2:ℝ)^(n/v)*Real.exp b)*(R^v * Real.exp b)):=by
  have he:=Nat.div_add_mod n v
  have ht: 0 ≤ R:= zero_le_one.trans hv
  have hh: Own f δ b B (M^n) (((1/2:ℝ)^(n/v)*Real.exp b)*(R^(n%v) * Real.exp b)):=by
    have hy: Own f δ b B ((M^v)^(n/v)) ((1/2:ℝ)^(n/v)* Real.exp b):=by simpa only [← Pi.pow_apply] using (Heritage.power hq hd hb (by norm_num) (n/v))
    have hx: Own f δ b B (M^(n%v)) (R^(n%v)* Real.exp b):=by simpa only [← Pi.pow_apply] using (Heritage.power hu hd hb ht (n%v))
    nth_rw 1 [← he]; rw [pow_add,pow_mul]; exact hy.meet hx hd hb (by positivity) (by positivity)
  refine hh.mono ?_; gcongr; exact (Nat.mod_lt _ hp).le
lemma rate_own (hu : Own f δ b B M R) (hq : Own f δ b B (M^v) (1/2)) (hp : 0<v) (hv : 1≤R) (hd : 0<δ) (hb : 0≤b)
    (hg : 1/2 < g^v) (hg0 : 0<g) (hg1 : g<1) (n : ℕ): Own f δ b B (M^n) ((Real.exp b)^2*R^v / g^v*g^n):=by
  refine (c_n hu hq hp hv hd hb n).mono ?_
  have hh : 0≤R:=zero_le_one.trans hv
  have ht : (1/2:ℝ)^(n/v) ≤ g^n / g^v:=by
    rw [le_div_iff₀ (by positivity)]; refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hg.le _) (by positivity)) ?_; rw [← pow_mul,← pow_add]; apply pow_le_pow_of_le_one hg0.le hg1.le; have :=Nat.div_add_mod n v; have :=Nat.mod_lt n hp; omega
  rw [div_mul_eq_mul_div]; calc _ ≤ (g^n/g^v*Real.exp b)*(R^v*Real.exp b) := by gcongr
                                 _ = _:= by ring
variable (P : Plan j)

def spendV (w : ℝ) (L : Side) (b c C : ℝ) (n : ℕ) := Real.exp b+w*(4*padage P b c C n+tubeY L b c j n ^ 2)

lemma obtain_powers (b : ℝ) (hb : 0≤b) (L : Side): ∃ δ b₀ c C w q g R V : ℝ,∃ M r v : ℕ,
    0<w ∧ 0<δ∧Quota P b₀ b c C r ∧ δ≤b₀ ∧ 2*r≤ M ∧ -- c needs existential
    0≤q∧ q<1∧0<g∧g<1∧0<R ∧ V=spendV P w L b c C r∧∀ (F : Flight j k) (_:F.L=L) (s f : Side) (h:f.val=s.val*F.L.val) (B:ℕ),M≤ B →∀ t,
      let X : St f := fun U=> notch w (vaultF P F h t U)
      (∀ U,‖X U‖≤ q) ∧ Own f δ b B (X^v) (1/2) ∧ 0<v ∧ ∀ i, Own f δ b B (X^i) (R*g^i):= by
  obtain ⟨w,q,hp,hq,ht,H⟩:= prize (k:=k) P L
  obtain ⟨c,C,n,d,hbK⟩:= quantified P b hb
  let R:= max (spendV P w L b c C n) 1
  have hr:1≤R:=le_max_right ..
  have hR:0<R:=zero_lt_one.trans_le hr
  obtain ⟨δ,hδ,hδ',v,hv,m,hm,hQ⟩:= alteration hb hbK.hd hbK.hc hR hq ht 6 (12+6*arctic L j) (2*n)
  have hG : ∀ᶠ g : ℝ in 𝓝[<] 1,1/2<g^v:= ((continuous_id (X:=ℝ)).pow v).continuousAt.continuousWithinAt.eventually (lt_mem_nhds (show (1/2:ℝ)< ((1:ℝ)^v) by norm_num))
  obtain ⟨g,h₁,h₂,h₃⟩:= (hG.and ((show ∀ᶠ g:ℝ in 𝓝[<] 1, 0<g from mem_nhdsWithin_of_mem_nhds (lt_mem_nhds (by norm_num))).and self_mem_nhdsWithin)).exists
  refine ⟨δ,d,c,C,w,q,g,Real.exp b^2*R^v/g^v, _,m,n,v,hp,hδ,hbK,hδ',hm,hq,ht,h₂,h₃,by positivity,rfl,?_⟩
  intro F hL s f h B hB t X
  have hz : ∀ p:ℕ, ∃ Y,Sample d b c B X Y R p (6*p+(12+6*arctic L j)) := by
    intro p; obtain ⟨Z,hs⟩:= notched (p:=p) t P hbK (hm.trans hB) F h w hp; subst L; unfold R spendV -- dependent!
    exact ⟨_, hs.mono (le_max_left ..) (by omega)⟩
  have hi := H F hL s f h t
  have hu : Own f δ b B (X^v) (1/2) := hQ B hB f X hz hi
  obtain ⟨X',hh⟩:=hz 0; exact ⟨hi,hu,hv,fun i=> (rate_own (hh.all.1.clip hδ') hu hv hr hδ hb h₁ h₂ h₃ _)⟩
end YM.QCD.Run
