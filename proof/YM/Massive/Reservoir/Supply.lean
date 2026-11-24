import YM.Massive.Reservoir.Cards
/-! # Arcade, accumulate then obtain **one sequence**, simultaneous all
(incl bounded Borel) observable pencils at all resolutions. Strengthens
prior UV work from `YM/QCD/Agate/Pillar` (ultrafilter existence evocation). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Cascade
open QCD QCD.Lat Lattice Wilson RG Pressure Gauge Function Filter Set QCD.Tide QCD.Rain QCD.Plum QCD.Agate QCD.Acre QCD.Acre.Rails QCD.Acre.Rails.Reference
open IV QCD.Agate.Supply QCD.Sparks QCD.Land
open MeasureTheory
open scoped Topology Matrix.Norms.L2Operator BigOperators Classical ComplexOrder
variable {n F : ℕ}{J: Patch}{K: KernelChoices}(h:J.Branches K su)(B:SparkMesh)
variable (N p:ℕ→ℕ)(A:∀ i,Run (fixed J K h) (N i) (B.n (p i)) F)
variable (u e :ℕ→ℝ)(v:ℝ)
set_option quotPrecheck false
local notation "S"=> fixed J K h
local notation "s" => fun i m : ℕ=>(fixed J K h).side (B.n (p i)) m
variable {u e v} (ht: Arcade h B N p A u e v)
variable (X:ℕ→ScaleF F)(V W:ℕ→ℝ)(Ω:Ultrafilter ℕ)(hQ:(Ω:Filter ℕ)≤atTop)
local notation "sp"=> sight h B N p A
include ht hQ
lemma merge (m:ℕ) : ∃ V:ScaleF F,∀ D:Lot,∀ x:Malt D F, Tendsto (sp x m) (Ω:Filter ℕ) (𝓝 (V.mass D x)):=by
    have hv (D:Lot)(x:Malt D F) :∃ z:ℂ, Tendsto (sp x m) (Ω:Filter ℕ) (𝓝 z):=by
        obtain ⟨r,hr⟩:=encompassed D; obtain ⟨z,hz,hX⟩:=IV.mantic Ω hQ (Metric.closedBall (0:ℂ) (quota J (2*r+1) (u m)*Supply.budget x)) (isCompact_closedBall ..) (sp x m) ((sights h B N p A ht m r hr).mono fun i hi=>Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact (hi x).1)); exact ⟨z,hX⟩
    choose z H using hv; have ho:=ht.pace.tendsto_atTop.eventually (eventually_ge_atTop m); have h1(D:Lot)(x y:Malt D F) : z D (x+y)=z D x+z D y:=by
        apply tendsto_nhds_unique (H _ _); refine ((H D x).add (H D y)).congr' (hQ (ho.mono fun i hi=> (sAdd h B N p A ht x y hi).symm))
    have h2(D:Lot)(x:Malt D F)(q:ℂ) : z D (q • x)=q • z D x:=by
        apply tendsto_nhds_unique (H _ _); exact (tendsto_const_nhds.smul (H D x)).congr fun i=> (sMul h B N p A x q i m).symm
    let L(D:Lot): Malt D F→ₗ[ℂ]ℂ:= ⟨⟨z D,h1 D⟩,fun c x=> h2 D x c⟩ -- structure ext?
    refine ⟨⟨L,?_ , ?_, ?_⟩, H⟩
    · intro D; obtain ⟨r,hr⟩:= encompassed D; exact ⟨quota J (2*r+1) v,(Real.exp_pos _).le,fun x w hw=> le_of_tendsto (H D x).norm (hQ ((sights h B N p A ht m r hr).mono fun i Hi=> (Hi x).2 w hw))⟩
    · intro X D hj x; apply tendsto_nhds_unique (H D (wheel hj x)); apply (H X x).congr; intro i; unfold sight; rw [wheeling]
    · intro D; exact tendsto_nhds_unique (H D (1:Malt D F)) (tendsto_const_nhds.congr' (hQ (ho.mono fun i hi=> (sOne h B N p A ht D hi).symm)))
lemma article : ∃ X:ℕ→ScaleF F,∃ V W:ℕ→ℝ, Glacial h B N p A (Ω:Filter ℕ) X V W ∧ Yield X u J v:=by
    choose P H using merge h B N p A ht Ω hQ; let f(m i:ℕ):ℝ×ℝ:= ((A i).β m, (A i).w m); let B(m:ℕ):= (Set.Icc 1 (e m)) ×ˢ Icc (1/2:ℝ) 2 -- B shadow bug
    choose w hw H' using fun m:ℕ=> IV.mantic Ω hQ (B m) (show IsCompact (B m) from isCompact_Icc.prod isCompact_Icc) (f m) ((ht.pace.tendsto_atTop.eventually (eventually_gt_atTop m)).mono fun i hi=>⟨ht.base i m hi.le,ht.factor i m hi⟩)
    refine ⟨P,Prod.fst ∘ w,Prod.snd ∘ w,⟨H',H⟩,⟨fun m D x r hr=>?_⟩⟩; have hy:=(H m D x).norm; have hR:=sights h _ N p A ht m r hr; exact ⟨le_of_tendsto hy (hQ (hR.mono fun i Hi=> (Hi x).1)),fun w hw=> le_of_tendsto hy (hQ (hR.mono fun i Hi=> (Hi x).2 w hw))⟩
omit hQ
/-- Promotes convergence on a countable dense set in `L¹`-cost to convergence
on ALL the bounded Borel gauge-invariant tests. -/
lemma prominent {D:Lot}(m:ℕ)(P:Malt D F)(Y:ScaleF F)(r:ℕ)(hs:D⊆Lattice.box r)
    (f:ℕ→ℕ)(hf:StrictMono f)
    (X:ℕ→Malt D F)
    (he: ∀ w:ℝ,0<w→ ∃ i, Supply.budget (P-X i)<w)
    (hP: ∀ i,Tendsto (sp (X i) m ∘ f) atTop (𝓝 (Y.mass D (X i))))
    (hY: ∀ x:Malt D F, ‖Y.mass D x‖≤ quota J (2*r+1) (u m)*Supply.budget x) : Tendsto (sp P m ∘ f) atTop (𝓝 (Y.mass D P)):=by
    apply Metric.tendsto_nhds.mpr; intro ε hε; let z:= ε/3; let q:=quota J (2*r+1) (u m); have hz:0<z:=by unfold z; positivity
    have hq:0<q:=Real.exp_pos _; obtain ⟨i,hi⟩:= he (z/q) (div_pos hz hq)
    have hv:q*Supply.budget (P-X i)< z:=by rw [mul_comm]; exact (lt_div_iff₀ hq).1 hi
    let Q:= Y.mass D; let H(D': Malt D F)(i:ℕ):= sp D' m (f i)
    have hL: ∀ᶠ j:ℕ in atTop, dist (H (X i) j) (Q (X i))<z:=Metric.tendsto_nhds.mp (hP i) z hz
    have h0:=hf.tendsto_atTop
    filter_upwards [hL,h0.eventually ((ht.pace.tendsto_atTop).eventually (eventually_ge_atTop m)), h0.eventually (sights h B N p A ht m r hs)] with j h1 h2 h3
    have hV: dist (H P j) (H (X i) j) < z:=by rw [dist_eq_norm, show H P j-H (X i) j= _ from (sSub h B N p A ht P (X i) h2).symm]; exact ((h3 (P-X i)).1).trans_lt hv
    have hh: dist (Q (X i)) (Q P)< z:=by rw [dist_comm,dist_eq_norm,←map_sub]; exact (hY (P-X i)).trans_lt hv
    change dist (H P j) (Q P) < ε; have hA:= dist_triangle (H P j) (H (X i) j) (Q P); have hB:=dist_triangle (H (X i) j) (Q (X i)) (Q P); unfold z at *; linarith only [hA,hB,h1,hV,hh]
lemma serial : ∃ f:ℕ→ℕ,∃ X:ℕ→ScaleF F,∃ V W:ℕ→ℝ, StrictMono f ∧ Glacial h B (N∘f) (p∘f) (fun i=> A (f i)) atTop X V W ∧ Yield X u J v:=by
    let Ω:= Ultrafilter.of (atTop:Filter ℕ); obtain ⟨X,V,W,H,hV⟩:= article h B N p A ht Ω (Ultrafilter.of_le _); choose r hr using fun D:Lot=> Supply.books D F
    let T:= ℕ × Lot × ℕ; let C:= (ℕ→ℝ×ℝ) × (T→ℂ); let x(i:ℕ)(j:T):= sp (r j.2.1 j.2.2) j.1 i; let v₀(j:T):= (X j.1).mass j.2.1 (r j.2.1 j.2.2); let Ψ(i:ℕ)(m:ℕ):=((A i).β m,(A i).w m); let ξ:C:=(fun m=>(V m,W m),v₀)
    have hQ : Tendsto (fun i:ℕ=> (Ψ i,x i)) (Ω:Filter ℕ) (𝓝 ξ):=(show Tendsto Ψ (Ω:Filter ℕ) (𝓝 ξ.1) from tendsto_pi_nhds.mpr H.sites).prodMk_nhds (tendsto_pi_nhds.mpr fun i:T=> H.cylinders ..)
    obtain ⟨f,hf,hZ⟩:= (hQ.mapClusterPt.mono (Ultrafilter.of_le (atTop:Filter ℕ))).tendsto_subseq; have hx: Tendsto (Ψ∘f) atTop (𝓝 ξ.1):=(continuous_fst.tendsto _).comp hZ; have hY: Tendsto (x∘f) atTop (𝓝 ξ.2):= (continuous_snd.tendsto _).comp hZ; refine ⟨f,X,V,W,hf,⟨tendsto_pi_nhds.mp hx,?_⟩,hV⟩; intro m D P; obtain ⟨v,hv⟩:= encompassed D; exact prominent h B N p A ht m P (X m) v hv f hf (r D) (hr D P) (fun i=> tendsto_pi_nhds.mp hY (m,D,i)) (fun x=>(hV.costs m D x v hv).1)
end YM.Massive.Cascade
#print axioms YM.Massive.Cascade.serial
