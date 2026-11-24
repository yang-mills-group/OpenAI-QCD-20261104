import YM.Fir.Pearl
/-! For any point prototype, mesh estimates pass simultaneously along sequence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology BigOperators
variable {C:Sequence} {P:Calibration C} {β e:ℝ}(hp:C.Path β e) {n:ℕ}
variable (D:Fin n→ℕ)(u:(i:Fin n)→Label (D i))
variable (G:∀ d,Cottage P d) (hr:Sway C.S) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) (x:Points n)(hx:x∈conf n)
abbrev reading (P:Calibration C)(D:Fin n→ℕ)(u:(i:Fin n)→Label (D i))(p:Fin n)(i:ℕ):stalk C i:= stem P (D p) i (u p)


noncomputable abbrev looking (P:Calibration C)(D:Fin n→ℕ)(u:(i:Fin n)→Label (D i))(i:ℕ)(p:FrameI n→ ℤ): ℂ:= aperture C (reading P D u) i ((jade n).symm p)
include hp hr G hx hφ
set_option quotPrecheck false
local notation "U"=>reading P D u
local notation "S" i:arg=> C.S.spacing (C.N (φ i))
private lemma buying (s:Fin n)(b:Axis):∃ T:ℝ,0≤T∧∀ᶠ p in Watch C φ x, ‖tube C (reading P D u) s (fun i=> lDer C i b (reading P D u s i)) (φ p.1) p.2‖≤T:=by
      let R:=(D s)+2; let w:(i:ℕ)→stalk C i:=fun i=> lDer C i b ((reading P D u) s i)
      obtain ⟨z,hz⟩:=crossP hp hr (D s) G (u s) R le_rfl b
      have hu(k:Fin n): LightP C (reading P D u k):= ((G _).pointsP hp hr none (fun _=> u k) ⟨_,norm_nonneg (u k),Eventually.of_forall fun _=> le_rfl⟩).1
      let V:= glass G R z
      have h:= snow hp U w s G hφ x hx z hz (fun k _=> hu k)
      obtain ⟨B,hB,hv⟩:= forest hp (update U s V) hr hφ x hx (fun k=> by
           by_cases hh:k=s; · rw [hh,update_self]; exact lively hp G hr R z hz.cost
           rw [update_of_ne hh]; exact hu _)
      refine ⟨1+B,add_nonneg zero_le_one hB,?_⟩; filter_upwards [hv,h.eventually (closedBall_mem_nhds 0 zero_lt_one)] with p hv he; let H:= tube C U s V (φ p.1) p.2; let T:=tube C U s w (φ p.1) p.2; have h:‖T-H‖ ≤ 1:=by rw [← dist_zero_right]; exact Metric.mem_closedBall.mp he
      have ht :=(norm_add_le (T-H) H).trans (add_le_add h (show ‖H‖ ≤ _ from hv)); rw [sub_add_cancel] at ht; exact ht
lemma charged : quiet (fun i=> S i) (fun i=> looking P D u (φ i)) ((crossing n) x) := by
      choose L hL H using fun b:FrameI n=> buying hp D u G hr hφ x hx b.1 b.2
      let T:= ∑ i:FrameI n,L i
      apply Quiet.from_damp (fun _=> space0 _ _); let z:=crossing n x; let Vv:=noteF (fun i=>imageF (S i)) z
      obtain ⟨r,hr,hF⟩:= circles (v:=fun i=> imageF (S i)) ((rouses (C:=C) (φ:=φ) x).eventually (eventually_all.mpr H)); refine ⟨r,T,hr,Finset.sum_nonneg fun i _=> hL i,hF.mono (fun i hi p hg b=>?_ )⟩
      let k:= φ i; obtain ⟨s,B⟩:= b; let y:= (jade n).symm p; let a:= S i; have h1:0<a:=space0 _ _
      let A:= advanceF (s,B) p; have hh:(jade n).symm (advanceF (s,B) p)= advanced s B y:=by apply (jade n).injective; rw [brightF]; unfold y; simp
      have hp:= hi p hg (s,B); rw [raises,norm_smul,← dist_eq_norm] at hp; change ‖a⁻¹‖ * dist (aperture C U k (advanced s B y)) (aperture C U k y)≤ L (s,B) at hp; rw [Real.norm_of_nonneg (inv_pos.mpr h1).le,mul_comm a⁻¹,←div_eq_mul_inv,div_le_iff₀ h1] at hp
      change dist (aperture C U k ((jade n).symm (advanceF (s,B) p))) (aperture C U k y) ≤T*a; rw[hh]; exact hp.trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun b _=> hL b) (Finset.mem_univ _)) h1.le)
-- late pulse path.Price.
end YM.Massive.Fir
#print axioms YM.Massive.Fir.charged
