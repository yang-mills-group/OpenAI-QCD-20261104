import YM.QCD.Spice.Broom
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G₀:Flight j k}{h:f.val=c.val*G₀.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G₀ h
-- Φ_Error coarse plank via Gates. Real test applied to EvenA, CL from Even if desired.
variable {D E J:Type}
variable {μ : D→ℝ} {L:Ratio c f} (G : Send L F D)(P:Rise f F E J) -- shadows
variable (s:Finset (Fj D E J))(U V:Grid f)
local notation "X"=> EvenA f F
local notation "Y"=> EvenA c F
local notation "K"=> coreW G P s
local notation "K'"=> hooks (F:=F) L K
local notation "m"=> ops s
noncomputable def roundV (U:Grid f)(s:Finset (Fj D E J)): EvenA f F→L[ℂ]EvenA c F := LinearMap.toContinuousLinearMap {
    toFun:=fun x=> accord L F (G.shortP U) ⟨axle G U s (near (Modes f F) (Modes c F) x.val), (forces G P U s).evenPay (bright (ahead L F x)) ⟩
    map_add' := by
        intro x y; apply Subtype.ext; change wipe (Modes f F) (Modes c F) (G.shortP U) (axle G U s (near (Modes f F) (Modes c F) (light _ (x + y))))=_; rw [map_add,map_add,map_add,map_add]; rfl
    map_smul' := by
        intro a x; apply Subtype.ext; change wipe (Modes f F) (Modes c F) (G.shortP U) (axle G U s (near (Modes f F) (Modes c F) (light _ (a • x))))=_; rw [map_smul,map_smul,map_smul,map_smul]; rfl }
lemma stampF (x:EvenA f F): light _ (roundV G P U s x)=wipe A B (G.shortP U) (axle G U s (near A B (light _ x))):=rfl
lemma pioneer (x:X) (h:Gated K x):
 axle G U s (near A B (light _ x)) ∈ region K':=by
    apply (forces G P U s).keeps (Subset.refl _); apply effects _ _ _ h; intro i hi; change embed _ (atom i)∈_; rw [embed_atom]; apply marked; change ha c f F i∈_; rw [hooked,rootA]; exact (mem_filter.mp hi).2
lemma gateR (x:EvenA f F)(h:Gated K x): Gated ((halo G.trim K).image L.parent) (roundV G P U s x):=by
    unfold Gated; rw [stampF]; apply effects _ _ _ (pioneer G P s U x h); intro i hi; rcases splits_index i with ⟨j,rfl⟩|⟨j,rfl⟩
    · change ha c f F j∈K' at hi; rw [hooked,rootA] at hi; rw [wiper]; apply Subalgebra.sum_mem; intro k _; by_cases hz:G.shortP U j k=0; · rw [hz,zero_smul]; exact Subalgebra.zero_mem _
      apply Subalgebra.smul_mem; apply marked; exact mem_filter.mpr ⟨mem_univ _, mem_image.mpr ⟨_,Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr hi) (G.sleeps j k U hz),L.embed_parent _⟩⟩
    change hb c f F j∈K' at hi; rw [hooked,rootB] at hi; rw [tails]; apply marked; exact mem_filter.mpr ⟨mem_univ _,mem_image.mpr ⟨_,halo_subset _ _ hi, L.embed_parent _⟩⟩
local notation "r"=> rateF c f F x y
lemma stars (hv:0<x)(hy:0<y)(z:EvenA f F): load (rateF c f F x y) (near A B (light _ z)) ≤ load (fun _=>x) (light _ z):=by
    apply ferry (near ..) (fun _=>hv) _ _ (boarded ..); intro i _; rw [show near A B (atom i)=atom _ from embed_atom (ha c f F) i, load_atom _ (fun i=> rate_ok i hv hy)]; exact (wagesA ..).le
lemma ready_tip (h:Peak G t x y ξ μ) (hp:Healthy t (brimW G P s) U) (i:R)(hi:i∈K'): load (fun _=>y) (wipe A B (G.shortP U) (atom i)) ≤ (rateF c f F x y) i:=by
    rcases splits_index i with ⟨i,rfl⟩|⟨i,rfl⟩
    · change ha c f F i∈K' at hi; rw [hooked,rootA] at hi; rw [rateF,wagesA]; exact full_tip h.cup _ _ (h.earn _ _ (hp.mono_left (by rw [brim_eq]; exact Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr hi))))
    rw [tails,load_atom _ (fun _=>h.cup),rateF,wagesB]
lemma rounding (h:Peak G t x y ξ μ) (hp:Healthy t (brimW G P s) U) (z:X) (he:Gated K z):
 load (fun _=>y) (light _ (roundV G P U s z))≤(∏ i∈ops s,μ i)*load (fun _=>x) (light _ z):=by
    rw [stampF]; have hh:Pledge r (axle G U s) (∏ i∈ops s,μ i):= pledge_spin _ _ _ _ (fun i _=> h.spare i U) _
    have hz:= (ferry (wipe A B (G.shortP U)) (g:=fun _=>y) (fun i=> rate_ok i h.bud h.cup) (ready_tip G P s U h hp) _ (pioneer G P s U z he)); apply hz.trans ((hh.rates _).trans (mul_le_mul_of_nonneg_left (stars (y:=y) (c:=c) h.bud h.cup z) hh.nn)); -- ?_
lemma billed (h:Peak G t x y ξ μ) (hh:Healthy t (brimW G P s) U)(hl: Healthy t (brimW G P s) V)(hx:0≤w)(hA:0≤v)
    (ht: Pledge (rateF c f F x y) (axle G U s - axle G V s) (w*∏ i∈m,μ i))
    (hp:∀ i∈K',load (fun _=>y) (wipe A B (G.shortP U) (atom i)-wipe A B (G.shortP V) (atom i)) ≤ v*rateF c f F x y i) (z:X) (he:Gated K z):
    load (fun _=>y) (light _ (roundV G P U s z-roundV G P V s z)) ≤ (((hooks (F:=F) L K).card:ℝ)*v+w)*((∏ i∈m,μ i)*load (fun _=>x) (light _ z)):=by
     let T i:=axle G i s (near A B (light _ z)); let S' i:= wipe A B (G.shortP i); let u:=S' U; let g:=S' V
     let a:=rateF c f F x y; let p:=∏ i∈m,μ i; let l:= load (fun _=>x) (light _ z)
     have hm q:= pioneer G P s q z he; let b (i:Keys c F):=y
     rw [map_sub,stampF,stampF]; rw [show u (T U)-g (T V)=(u (T U)-g (T U))+g (T U-T V) from (by rw [map_sub]; abel)]
     have hx' : Pledge a (axle G U s) p:=pledge_spin _ _ _ _ (fun i _=> h.spare i U) _
     have hf := stars h.bud (y:=y) h.cup z (c:=c); have hP:load a (T U)≤p*l:=(hx'.rates _).trans (mul_le_mul_of_nonneg_left hf hx'.nn)
     have hF: load a (T U-T V)≤w*p*l:=(ht.rates _).trans (mul_le_mul_of_nonneg_left hf ht.nn)
     apply (spawnA b _ _).trans
     apply (add_le_add ((roughG u g (K') (ready_tip G P s U h hh) (ready_tip G P s V h hl) hp (fun i=> rate_ok i h.bud h.cup) hA _ (hm U)).trans (mul_le_mul_of_nonneg_left hP (mul_nonneg (Nat.cast_nonneg _) hA))) ((ferry g (fun i=>rate_ok i h.bud h.cup) (ready_tip G P s V h hl) _ (Subalgebra.sub_mem _ (hm _) (hm _))).trans hF)).trans_eq; ring
end YM.QCD.Spice
