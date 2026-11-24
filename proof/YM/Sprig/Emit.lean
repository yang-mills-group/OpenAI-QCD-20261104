import YM.Sprig.Nose
/-! Sequences of actual resolved probes. Pencils retains epochs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder Interval
variable {C:Sequence} {D d d' n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Vale Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF Massive.Elm.SparK.Arbor.PlaneG
variable (A:Compass C D)
variable (φ:ℕ→ℕ)(Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
open Function Set Finset Metric Compass
noncomputable def Compass.mesh :ℝ:= Ibis.rescaling C.S A.ℓ A.r
-- Eventual laws tuned to support arbitrary sector extension. Poly ζ.
structure Canopy (P:Calibration C) (φ:ℕ→ℕ)(Q:Choir) where
   Pz :ℕ→ℕ
   B (k:ℕ):Compass C (Pz k)
   cc:ℕ→ℝ
   La(d:ℕ):Laurel d
   Ja(d:ℕ):Landing P.sym (La d)
   Km(d:ℕ):Pins d
   V:ℕ→∀ d,Label d→ₗ[ℂ] Label d
   trueK (k:ℕ): Known (B k)
   checkedW k: DiscP P (B k) φ (V k) Q
   wohlen (d:ℕ):∀ᶠ k in atTop,Inn P (B k) (Ja d)
   pins (d:ℕ)(v:Raw d): ∀ᶠ k in atTop,∃ h:d≤ Pz k,GlyphV ((Km d).f v) (Pz k) h ∈ (B k).Ω
   course : Tendsto (fun k=>(B k).r) atTop (𝓝 0)
   many : Tendsto (fun k=>(B k).K) atTop atTop
   epsilon : Tendsto (fun k=>(B k).e) atTop (𝓝 0)
   reach : Tendsto (fun k=>(B k).v) atTop atTop
   charge (k:ℕ): 1 ≤ cc k
   climb : Tendsto cc atTop atTop
   bounded (k:ℕ): (B k).dB ≤ cc k
   shots (n:ℕ): Tendsto (fun k=> (cc k)^n*(B k).bid) atTop (𝓝 0)
   neighbors (n:ℕ): Tendsto (fun k=> (cc k)^n*(B k).mesh) atTop (𝓝 0)
namespace Canopy
variable {P φ Q}(E:Canopy P φ Q)
noncomputable abbrev cut (k:ℕ)(p:Label d):= choiceT (E.V k) Q p
set_option quotPrecheck false
local notation "VZ" i:arg=> E.B i
variable (t:Text d) (l:Σ d:ℕ,Text d)
abbrev Texts := Σ d:ℕ,Text d
noncomputable abbrev Loaded (t:Texts):Prop:= t.2.mark≠0∧∀ᶠ k in atTop, ∃ h:t.1 ≤ E.Pz k,GlyphV t.2 _ h ∈ (E.B k).Ω
noncomputable def act(k:ℕ)(t:Texts):Q.W:= E.cut k t.2.mark
local notation "H"=> Loaded E
lemma vouchers (i:Raw d): Loaded E ⟨d,(E.Km d).f i⟩:=by refine ⟨?_,E.pins d i⟩; change ((E.Km d).f i).mark≠0; rw [←(E.Km d).idV]; apply Module.Basis.ne_zero
lemma here (i:Stokes d): Loaded E ⟨d,(E.La d).F i⟩:= ⟨Vale.living _ i,(E.wohlen d).mono fun k h=>⟨h.level,(h.rich i).1⟩⟩
noncomputable def lifted(i:Stokes d):Texts:=⟨d,(E.La d).F i⟩
lemma pays(i:Stokes d): Loaded E (lifted E i):= here E i
variable (x: Texts)(h:Loaded E x)
include hQ h
lemma seconds (a:Axis) : ∃ T:ℝ,0 ≤ T∧∃ g:ℕ→ Stokes (x.1+2)→ℂ,∀ᶠ k in atTop, (∀ i:Stokes (x.1+2),‖g k i‖ ≤ T)∧bright Q (E.B k).r a (act E k x)=∑ i: Stokes (x.1+2),g k i • act E k (lifted E i):=by
     let L:=x.1+2; let f:=x.2; let t:=E.La L; let J:=E.Ja L
     let T:= money P t J a f
     have hv:∀ᶠ k in atTop,∃ y:Stokes (x.1+2)→ℂ, ‖y‖ ≤ T∧bright Q (E.B k).r a (act E k x)=∑ i: Stokes (x.1+2),y i • act E k (lifted E i):=by
            filter_upwards [E.wohlen L,h.2] with k hk hu; obtain ⟨hc,he⟩:=hu; exact expenses P (E.B k) φ (E.V k) Q hQ (E.checkedW k) t J hk a x.2 rfl hc he h.1
     obtain ⟨N,hN⟩:= eventually_atTop.mp hv; choose! y hf hP using hN; have hp:= (hf N le_rfl); exact ⟨T,(norm_nonneg _).trans hp,y,eventually_atTop.mpr ⟨N,fun i hi=>⟨fun j=> (norm_le_pi_norm (y i) j).trans (hf i hi), hP i hi⟩⟩⟩
omit hQ h
lemma copperP {n:ℕ} (v:Fin n→ Texts)(hx:∀ i,Loaded E (v i)): ∀ᶠ k:ℕ in atTop, ∃ F:(i:Fin n)→(v i).1 ≤E.Pz k,∀ i:Fin n,GlyphV (v i).2 (E.Pz k) (F i)∈ (E.B k).Ω:=by
    filter_upwards [eventually_all.mpr fun i=>(hx i).2] with k hp; choose g hg using hp; exact ⟨g,hg⟩
noncomputable abbrev boreK (k:ℕ)(a b:ℝ) := {x:Points n | x.ofLp∈Ibis.flats (Fin n) (a*(E.B k).e) (b*(E.B k).v)}
-- fix gauge factor b = .1 for interior.Gn.Cert.C
lemma care (S:Set (Points n))(hs:IsCompact S)(ht:S⊆conf n)(a b:ℝ)(ha:0<a)(hb:0<b):∀ᶠ i:ℕ in atTop,S⊆boreK E i a b:=by
     let f := fun p:Points n=> p.ofLp; have hc:Continuous f:= PiLp.continuous_ofLp ..
     obtain ⟨R,hR⟩:= ((hs.image (continuous_norm.comp hc)).bddAbove)
     let l:=E.B; have hP:= (E.reach).eventually_gt_atTop (2*R/b); let T:=(fun i=>a*(E.B i).e); have h0:Tendsto T atTop (𝓝 0):=by simpa only [mul_zero] using E.epsilon.const_mul a
     by_cases he:S.Nonempty; swap; · rw[Set.not_nonempty_iff_eq_empty] at he; rw [he]; exact Eventually.of_forall fun i=>empty_subset _
     let I:= {v:Fin n×Fin n// v.1≠v.2}; have hf(j:I):∀ᶠ i in atTop,∀ x∈ S,T i≤ ‖x j.val.1-x j.val.2‖:=by
          let f(x:Points n):= ‖x j.val.1-x j.val.2‖; obtain ⟨x,hx,h⟩:=hs.exists_isMinOn he (show ContinuousOn f S from (show Continuous f by unfold f; fun_prop).continuousOn); have hp:0<f x:= norm_pos_iff.mpr (sub_ne_zero.mpr ((show Injective x.ofLp from ht hx).ne j.property)); exact (h0.eventually_le_const hp).mono fun i h1 p hp=> h1.trans (h hp)
     filter_upwards [hP, eventually_all.mpr hf] with i hI hh p hp; refine (outward ..).2 ⟨?_,fun j k hv=> hh ⟨(j,k),hv⟩ p hp⟩; have hv:‖p.ofLp‖ ≤R:= hR ⟨p,hp,rfl⟩; have h:2*R<(l i).v*b:= (div_lt_iff₀ hb).1 hI; change _ ≤ b*(l i).v/2; linarith
lemma sequels {n:ℕ} (u:Fin n→ Texts)(hf:∀ i,Loaded E (u i))(K:Set (Points n))(hk:IsCompact K)(hy:K ⊆ conf n):∀ᶠ i:ℕ in atTop,∀ y∈K, ‖blast Q (E.B i).r (fun j=> act E i (u j)) y‖ ≤ E.cc i^n:=by
     filter_upwards [copperP E u hf, E.care K hk hy 3 (1/4) (by norm_num) (by norm_num), E.many.eventually_ge_atTop n] with i h1 h2 h3 y h
     obtain ⟨F,hF⟩:=h1; let v(j:Fin n):= GlyphV (u j).2 _ (F j); have hp:= h2 h
     have hr:= (E.checkedW i).life n v hF (fun k=>(hf k).1) h3 y.ofLp (show y.ofLp∈ _ from ?_); swap
     · rw [show (E.B i).v/4=(1/4)* (E.B i).v from (by ring)]; exact hp
     apply hr.trans; exact pow_le_pow_left₀ (zero_le_one.trans (Ibis.gold0 ..)) (E.bounded i) n
end Canopy
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Canopy.seconds
#print axioms YM.Intag.Sprig.Canopy.sequels
#print axioms YM.Intag.Sprig.Canopy.wohlen
