import YM.QCD.Spice.Fleece
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G₀:Flight j k}{h:f.val=c.val*G₀.L.val}
-- Φ_Error coarse plank via Gates. Real test applied to EvenA, CL from Even if desired.
variable {D E J:Type}
variable {μ : D→ℝ} {L:Ratio c f} (G : Send L F D)(P:Rise f F E J) -- shadows
variable (s:Finset (Fj D E J))(U V:Grid f)
lemma twiceCow {I:Type*}[Fintype I](f:I→ℝ)(x: Patio I)(z:ℝ)(h: load f (light _ x) ≤ z): load f (light I (NormedSpace.exp x-1-x))≤ Real.exp z*z^2:=by
    simp only [map_sub,map_one,light_exp]; let x':= light I x; let T (n:ℕ): Alg I:= (n.factorial:ℂ)⁻¹ • x'^n; let V (n:ℕ):=(n.factorial:ℝ)⁻¹*z^n
    have hz:0≤z:=(load_nn ..).trans h; have ht : HasSum T (NormedSpace.exp x'):=exp_series_hasSum_exp' x'
    have hp : HasSum V (Real.exp z):=by rw [Real.exp_eq_exp_ℝ]; exact exp_series_hasSum_exp' (𝕂:=ℝ) z
    rw [←hasSum_nat_add_iff' (k:=2),sum_range_succ,sum_range_one,show T 0=1 from (by simp [T]),show T 1= x' from (by simp [T]),sub_add_eq_sub_sub] at ht
    have he n : load f (T n)≤V n := by
      have hv n:load f (x'^n)≤z^n:=by induction n with
        | zero=> simp [load_one]
        | succ n ih=> rw [pow_succ,pow_succ]; exact (load_mul ..).trans (mul_le_mul ih h (load_nn ..) (pow_nonneg hz _))
      dsimp only [T,V]; rw [load_scale]; simpa using mul_le_mul_of_nonneg_left (hv n) (by positivity : 0 ≤ (n.factorial:ℝ)⁻¹)
    exact le_of_tendsto_of_tendsto' ((payload f).continuousAt.tendsto.comp ht) (hp.mul_right (z^2)) (fun s:Finset ℕ=> (load_sum f s (fun n=> T (n+2))).trans (sum_le_sum fun k _=>(he _).trans (show V (k+2) ≤ V k*z^2 from by
       unfold V; rw [pow_add,←mul_assoc]; gcongr <;> first | positivity | omega ))) -- factorial syntax
local notation "A"=> coreW G P s
lemma maskingW (hk:spent s=∅): hue G P t s= RG.masked t (brimW G P s) (dye G P t s):=by
   funext U; have hf : P.spare (spent s):=by simp [hk,Rise.spare]
   have hh:closeS G P t s U ↔ Healthy t (brimW G P s) U:=by rw [closeS,hk, show P.wish ∅=∅ by simp [Rise.wish]]; simp only [Healthy, Finset.disjoint_iff_inter_eq_empty]; rw [inter_comm,eq_comm]
   simp_rw [hue,hf,true_and,hh]; by_cases ho: Healthy t (brimW G P s) U
   · exact (if_pos ho).trans (masked_eq _ _ _ _ ho).symm
   exact (if_neg ho).trans (masked_ne _ _ _ _ ho).symm
variable (h₀:Healthy t (brimW G P s) U)(h₁:Healthy t (brimW G P s) V)(hp:Peak G t x y ξ μ)
variable {z z':ℝ}{i:E}
lemma madeW (he:leftE s={i})(hk:spent s=∅): dye G P t s U= roundV G P U s (NormedSpace.exp (P.reading t U i)-1) :=by
   apply Subtype.ext; change light _ (dye G P _ _ U)=light _ (roundV G P U s _)
   rw [stampF,dipping,made,he,hk,prod_singleton,prod_empty,mul_one] -- check light after
lemma wore (h:P.Wave t)(hs:leftE s={i}): Gated (coreW G P s) (P.reading t U i):= gateMon _ _ (fun j hj=> mem_biUnion.mpr ⟨Sum.inr (Sum.inl i), by
                 have he : i∈leftE s:=by rw [hs]; exact mem_singleton_self _
                 simpa [leftE] using he, hj⟩) _ (P.readable t h ..)
include h₀ hp in
lemma rearE (hs:leftE s={i}) (hk:spent s=∅)(h:P.Wave t)(hh: load (fun _=>x) (light _ (P.reading t U i))≤z):
    Gated ((halo G.trim (coreW G P s)).image L.parent) (dye G P t s U-roundV G P U s (P.reading t U i)) ∧
    load (fun _=>y) (light _ (dye G P t s U-roundV G P U s (P.reading t U i)))≤ (∏ i∈ops s,μ i)*(Real.exp z*z^2):=by
       rw [madeW G P s U hs hk,← map_sub]; have hw:= wore G P s U h hs; have he : Gated (coreW G P s) (NormedSpace.exp (P.reading t U i)-1-P.reading t U i):=by unfold Gated; rw [map_sub]; exact Subalgebra.sub_mem _ (gate_exp _ _ hw) hw -- hw
       have hu:Pledge _ (axle G U s) (∏ i∈ops s,μ i):= pledge_spin _ _ _ _ (fun i _=> hp.spare i U) _
       exact ⟨gateR G P s U _ he,(rounding G P s U hp h₀ _ he).trans (mul_le_mul_of_nonneg_left (twiceCow _ _ _ hh) hu.nn)⟩
lemma onHealthy (h:Healthy t (brimW G P s) V)(he:leftE s={i}): P.reading t V i=P.main i V:=by
    have hx:_root_.id ( (P.row i).support ⊆ brimW G P s):=fun j hj=> native_sub G P s (mem_biUnion.mpr ⟨Sum.inr (Sum.inl i),by
        have ht : i∈leftE s:=by rw [he]; simp
        simpa [leftE] using ht, hj⟩)
    rw [P.hype]; exact if_pos (h.mono_left hx)
section
variable {T:Grid f→Sheet f}(C:Sun G₀ c f h δ v q u a l T)
local notation "D"=> C.equip F b
variable (e: Finset (Fj (Tr f) E J)) (hΓ:Peak (C.equip F b) t x y ξ (fun i=> Real.exp 1*terra C F b x y i))(ht:0≤u)(hy:y*fingers F*q ≤ ξ*x)(hc:∀ i,terra C F b x y i≤1)

-- evaluate at root V. use different mode estimates for non-short BIG. Area.Has mask(Y)
include hΓ ht hy hc in
lemma sparkler (he:leftE e={i})(hk:spent e=∅)(hh:P.Wave t)(h₁:Healthy t (brimW (C.equip F b) P e) V)(h₀:Healthy t (brimW (C.equip F b) P e) U)(hV:beamAt (brimW (C.equip F b) P e) U V w)(hw:0≤w)(ht':w<δ/2)(hs: load (fun _=>x) (light _ (P.reading t U i))≤z):
     let Z:=roundV (C.equip F b) P V e (P.reading t U i)
     let Y:= hue (C.equip F b) P t e U - Z; let μ:= fun i=>Real.exp 1*terra C F b x y i; let j:= w/(δ/2)
     Gated ((halo b (coreW (C.equip F b) P e)).image (sliceL G₀ h).parent) Y ∧ load (fun _=>y) (light _ Y)≤ ((∏ i∈ops e,μ i)*z)*(Real.exp z*z+(((hooks (F:=F) (sliceL G₀ h) (coreW (C.equip F b) P e)).card:ℝ)*(ξ*j)+(ops e).card*j)):=by
     intro Z Y μ p; let Y':=dye D P t e U; let A':=roundV D P U e (P.reading t U i); have hy':Y=(Y'-A')+(A'-Z):=by unfold Y; rw [maskingW D P e hk,masked_eq _ _ _ _ h₀]; unfold Y'; abel
     obtain ⟨h1,h2⟩:=rearE D P e U h₀ hΓ he hk hh hs; have hx:= wore D P e U hh he; have hP: Pledge _ _ _:= sassy C _ _ _ b P hΓ hV hw ht' hc; let v' := ∏ i∈ops e,μ i; have hΓ':0≤v':=prod_nonneg fun i _=> (hΓ.spare i U).nn -- implicit U
     have hE:0≤p:= div_nonneg hw (half_pos C.positive).le; have hξ:0≤ξ:= zero_le_one.trans hΓ.post
     let L:= ((hooks (F:=F) (sliceL G₀ h) (coreW D P e)).card:ℝ)*(ξ*p)+(ops e).card*p; have hm: load (fun _=>y) (light _ (A'-Z)) ≤ L*(v'*z):= (billed D P e U V hΓ h₀ h₁ (mul_nonneg (Nat.cast_nonneg _) hE) (mul_nonneg hξ hE) hP (fun i hi=> (swept C hΓ U V P e h₀ h₁ hV hw ht' ht hy i hi).2.2) _ hx).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hΓ') (by positivity))
     rw [hy']; constructor
     · unfold Gated; rw [map_add]; refine Subalgebra.add_mem _ h1 ?_; rw [map_sub]; exact Subalgebra.sub_mem _ (gateR D P e U _ hx) (gateR D P e V _ hx)
     rw [map_add]; apply (spawnA ..).trans; exact (add_le_add h2 hm).trans_eq (show v'*(Real.exp z*z^2) + L*(v'*z)=v'*z*(Real.exp z*z+L) by ring)
end
end YM.QCD.Spice
