import YM.Analysis.SmoothJets
import Mathlib.Topology.Sequences
/-!
  Joint mesh exposures. Not just convergence after rounding. This notion remembers
  fine displacements in `Cover` and doesn't conflate limit at collisions with a point moment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Fir
open Set Function Filter Metric
open scoped Topology
variable {X Y E: Type*} [TopologicalSpace X]
noncomputable abbrev noteF (v:ℕ→ Y→ X)(x:X): Filter (ℕ×Y):=
    comap (fun p=> p.1) atTop ⊓ comap (fun p=> v p.1 p.2) (𝓝 x)
noncomputable abbrev seesF {Z:Type*}[TopologicalSpace Z] (v:ℕ→Y→X) (f:ℕ→Y→Z)(x:X)(l:Z):Prop:= Tendsto (fun p=> f p.1 p.2) (noteF v x) (𝓝 l)
namespace NoteF
variable {v:ℕ→Y→X}{x:X}
lemma approach : Tendsto (fun p:ℕ×Y=>v p.1 p.2) (noteF v x) (𝓝 x):= tendsto_iff_comap.mpr inf_le_right
lemma beyond : Tendsto (fun p:ℕ×Y=>p.1) (noteF v x) atTop:=tendsto_iff_comap.mpr inf_le_left
lemma ride {A: Type*}{F: Filter A}(a:A→ℕ)(b:A→Y)(ht:Tendsto a F atTop)(hs:Tendsto (fun i=> v (a i) (b i)) F (𝓝 x)):Tendsto (fun i=> (a i,b i)) F (noteF v x) :=tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ht,tendsto_comap_iff.mpr hs⟩
lemma fullness {f:ℕ→ Y}(h:Tendsto (fun i=>v i (f i)) atTop (𝓝 x)): (noteF v x).NeBot:= (ride (fun i:ℕ=>i) f tendsto_id h).neBot
lemma surround {P:ℕ×Y→ Prop}: (∀ᶠ y in noteF v x,P y) ↔ ∃ u∈𝓝 x,∀ᶠ i in atTop,∀ z:Y,v i z∈u→ P (i,z):=by
    constructor
    · intro hy; obtain ⟨S,hS,T,hT,h⟩:= mem_inf_iff.mp hy
      obtain ⟨R,hR,hF⟩:= mem_comap.mp hS; obtain ⟨U,hU,hG⟩:= mem_comap.mp hT; exact ⟨U,hU,(show ∀ᶠ i in atTop,i∈R from hR).mono fun i hi z hz=> Eq.subset h.symm (show (i,z)∈ S∩T from ⟨hF hi,hG hz⟩)⟩ -- order binder R? 
    intro ⟨u,hu,h⟩; filter_upwards [(approach (v:=v)).eventually hu,(beyond (x:=x) (v:=v)).eventually h] with i hi hp; exact hp _ hi
lemma transported {Z:Type*}[TopologicalSpace Z]{V:Type*}{w:ℕ→ V→ Z} {x':Z} (G:ℕ→ ℕ)(g:ℕ→Y→V)(hG:Tendsto G atTop atTop) (K:X→ Z)(hK:ContinuousAt K x)(hp:K x=x')(hv:∀ᶠ p in noteF v x, w (G p.1) (g p.1 p.2)= K (v p.1 p.2)): Tendsto (fun p:ℕ×Y=> (G p.1,g p.1 p.2)) (noteF v x) (noteF w x'):=by
     subst x'; exact ride _ _ (hG.comp beyond) ((hK.tendsto.comp approach).congr' (hv.mono fun _ h=> h.symm))
end NoteF
namespace NoteF
variable [MetricSpace E]
lemma compactity {z:ℕ→ Y→ X}{f:ℕ→ Y→ E}{F:X→E}(K:Set X)(h:IsCompact K)(hf:ContinuousOn F K) (hs:∀ x∈K,seesF z f x (F x))(ε:ℝ)(ht:0 < ε):∀ᶠ i in atTop,∀ p,z i p∈K → dist (f i p) (F (z i p))≤ ε:=by
   -- finite subcover
   have h(x:X)(hx:x∈K):∃ u:{u:Set X// IsOpen u}, x∈(u:Set X) ∧ ∀ᶠ i in atTop,∀ p,z i p∈(u:Set X)→z i p∈K→dist (f i p) (F (z i p))≤ε:=by
       obtain ⟨U,hU,hz⟩:=NoteF.surround.mp ((hs x hx).eventually (Metric.closedBall_mem_nhds _ (half_pos ht)))
       have he:= (hf x hx).eventually (Metric.closedBall_mem_nhds _ (half_pos ht))
       obtain ⟨V,hV,H⟩:= mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
       obtain ⟨W,hW,hW',hw⟩:=_root_.mem_nhds_iff.mp (inter_mem hU hV); refine ⟨⟨W,hW'⟩,hw,hz.mono fun i hi p hg hhp=>?_⟩; have ha := (Metric.mem_closedBall.mp (hi p (hW hg |>.1))); have hb:= Metric.mem_closedBall.mp (H ⟨(hW hg).2,hhp⟩)
       have hv:= dist_triangle_right (f i p) (F (z i p)) (F x); exact hv.trans ((add_le_add ha hb).trans_eq (add_halves _))
   choose u hu hv using fun x:K=> h x.val x.property; obtain ⟨S,hS⟩:= ‹IsCompact K›.elim_finite_subcover (fun x:K=> (u x:Set X)) (fun i=> (u i).property) (fun x hx=>mem_iUnion.mpr ⟨⟨x,hx⟩,hu _⟩); filter_upwards [eventually_all.mpr (fun i:S=> hv i.val)] with i hi p hp; obtain ⟨r,hr⟩:= mem_iUnion.mp (hS hp); obtain ⟨he,ht⟩:= mem_iUnion.mp hr; exact hi ⟨_,he⟩ p ht hp
lemma circles {v:ℕ→Y→E}{x:E}{P:ℕ×Y→Prop}(h:∀ᶠ y in noteF v x,P y): ∃ r:ℝ,0 < r∧∀ᶠ i in atTop,∀ p:Y,v i p∈ball x r→P (i,p):=by obtain ⟨u,hu,h⟩:=surround.mp h; obtain ⟨r,hr,H⟩:=Metric.mem_nhds_iff.mp hu; exact ⟨r,hr,h.mono fun i hi p hp=>hi p (H hp)⟩
end NoteF
end YM.Fir
#print axioms YM.Fir.NoteF.compactity
