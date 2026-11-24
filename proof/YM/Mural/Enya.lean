import YM.Mural.Dune
/-!
# Two distinct certified supports, new-seed and ordinary peer transfers. Birth charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open YM.Next.Free
variable {c f:Side}{j k m:ℕ}
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG
set_option quotPrecheck false
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "L"=> L'.L
local notation "S"=> L'.visit K d
local notation "Ψ"=> sliceL L' d
local notation "M"=> arctic L j
variable {T: Tube su (L'.visit K d)}{T':Teller su}{Q:Target su T'}{v x₀ W μ C:ℝ} {o:Target.Order su W}
variable {U:RG.Rep su f}(H:Cash W x₀ μ L'.L Q o C T U)
variable (x y: Site c)(p q:Site f){N:ℕ}
local notation "Tx"=> texel L' d 0 x p
local notation "Ty"=> texel L' d 0 y q
local notation "Cq"=> cleared p q L' d x y
local notation "Lq"=> loaded p q L' d x y
local notation "Q0"=> (sliceL L' d).embed x
local notation "Yg"=> (sliceL L' d).embed y
local notation "B"=> radiusB x₀
local notation "A₀"=> Lattice.halo B {Q0}
lemma vistaU (o:Site f)(s t:Site f)(i:ℕ)(ht: separation o s+4*i ≤ B) (hp: separation s t≤ i): LocalOn (Lattice.halo B {o}) (apogee s t):= by
     intro U V h; apply congr_arg colour; apply travel_local s (cord s t); exact agrees_mono h (fun j hj=> halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle o s _).trans ((Nat.add_le_add_left ((Eyrie.walked _ _ _ (show j∈visits _ (cord s t) from hj)).trans (cord_len s t hp)) _).trans ht)⟩)
local notation "hvS"=> (FreeResolvent.Mid.upto)
variable (M₁:ℕ)
-- choose extents r pre-L. hB high clock. all locality EXACT when Mx fits halo
abbrev berthD (j:ℕ):= 16*(j+3)
local notation "σt"=> berthD j
variable (hv:separation ((sliceL L' d).embed x) p ≤ arctic L'.L j)(hw:separation ((sliceL L' d).embed y) q ≤ arctic L'.L j)
variable (hp:separation p q≤ berthD j)
include hv hw hp
lemma orbitB : separation x y≤ berthD j:=by
     have h: (Ψ).count.val*separation x y ≤ M+(σt+M) :=by -- p notation
        rw [← FreeResolvent.Mid.upto Ψ x y]; exact (separation_triangle ..).trans (Nat.add_le_add hv ((separation_triangle ..).trans (Nat.add_le_add hp ((separation_comm ..).trans_le hw))))
     have hh:3 ≤ L'.L.val:= L'.coarse
     apply Nat.le_of_mul_le_mul_left _ (by omega : 0 < L'.L.val)
     refine h.trans (?_)
     unfold berthD arctic; change 4*((j+3)*(L).val) +(16*(j+3)+4*((j+3)*(L).val)) ≤ L'.L.val *_; nlinarith only [hh,mul_le_mul_of_nonneg_right hh (Nat.zero_le (j+3))]
variable (hS: (berthD j)*L'.L.val +arctic L'.L j+4*(berthD j)≤ radiusB x₀)
local notation "gr"=>vap
include hS
lemma load_home : LocalOn A₀ Lq:=by
    intro U V h; let A(Q: Mat)(D:Mat)(X:Mat):=Q*X*star D
    have h₁:M≤ B:=by omega
    have hx:=respects L' d 0 x p B h₁ U V h
    have hy: separation Q0 Yg≤ σt * L'.L.val:=by
         rw [FreeResolvent.Mid.upto Ψ x y,mul_comm]; exact Nat.mul_le_mul_right _ (orbitB L' d x y p q hv hw hp)
    have hz : Ty U=Ty V:=respects L' d 0 y q M le_rfl _ _ (agrees_mono h (fun i hi=>by obtain ⟨x',hx',h'⟩:= halo_spec.mp hi; rw [mem_singleton.mp hx'] at h'; refine halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle _ Yg _).trans (?_)⟩; omega))
    unfold loaded; rw [hx,hz,vistaU Q0 p q σt (by omega) hp U V h]
-- near bound.T.Refresh weight definitions.EPlot revoke. use chamber layer witness. constant cost E.If.Depth.B.
variable {W0:Lat.Frame c} {F:Tree.Forest (L'.visit K d).ratio} {hw':LogField su c}{X:Grid f}{Y:Grid c}{a v r:ℝ}
noncomputable def fenceCharge (j:ℕ)(LX:Side)(R:ℝ):ℝ:= let C₀:= Flume.massL LX*R*arctic LX j; let s:= Kit.scale LX; (s*C₀+s*(s*(R*(4*berthD j:ℕ))+1*C₀))+(s^2*(R*(4*berthD j:ℕ)))
variable (hV:2* L'.patch.radius < f.val) (hB: Blanket (L'.visit K d) X Y x (4*radiusB x₀) W0 hw' v)(hz:∀ X:su.El,‖colour X-1‖≤ r*su.chord X)(h0:0 ≤v)(hr:0≤r)
local notation "sB"=> Kit.scale L
local notation "Vq"=> load_home
include hV hB h0 hr hz
lemma balance : ‖loaded p q L' d x y X-cleared p q L' d x y Y‖≤ fenceCharge j L r *v:=by
      let p₀:= constantGauge W0 (S).ratio; let U:= gauge p₀ X; let V:=gauge W0 Y
      have hk:p₀ ∘ (Ψ).embed=W0:=funext fun i=>congr_arg W0 ((Ψ).embed_parent _)
      have hU:‖Lq X-Cq Y‖ ≤ ‖Lq U-Cq V‖:=by
          rw [show Lq U=_ from load_frame p q p₀ L' d x y X, show Cq V=_ from clear_frame p q L' d x y Y W0, show p₀ Q0=_ from congr_fun hk x, show p₀ Yg=_ from congr_fun hk y, ← sub_mul,← mul_sub]; exact leaseX _ _ _
      have hC:(S).ratio=Ψ:=rfl; have h₁:0<B:=by unfold berthD at hS; omega
      have hi:=orbitB L' d x y p q hv hw hp
      have hE:separation Q0 Yg≤ σt*L'.L.val:=by rw [FreeResolvent.Mid.upto Ψ x y,mul_comm]; exact Nat.mul_le_mul_right _ hi
      have he: ∀ i:Site f,separation Q0 i ≤ B →∀ a:Axis,su.chord (U (i,a))≤ v:=by
          intro i h a; apply hB.fine; have hp:= Work.E04.parent_separation Ψ Q0 i; rw [Ratio.embed_parent] at hp; exact (hp.trans (show separation Q0 i+1 ≤ 4*B from by omega))
      have hw:= load_fit p q L' d x y hV U Q0 (by rw [separation_self]; omega) (by omega) (by omega) hp hr h0 hz he
      have hz': ‖Cq V-Cq 1‖≤ sB^2*(r*↑(4*σt:ℕ))*v :=by
          unfold cleared; rw [← smul_sub,norm_smul,remainsX]
          have hh:=cord_len x y hi; apply (mul_le_mul ?_ ?_ (norm_nonneg _) (sq_nonneg (sB))).trans_eq (show sB^2*(r*((4*σt:ℕ)*v))=sB^2*(r*↑(4*σt:ℕ))*v by ring)
          · rw [norm_mul,norm_star,pow_two]; exact mul_le_mul (light_bound p L' d x hV 0) (light_bound q L' d y hV 0) (norm_nonneg _) (Kit.scale_pos _).le
          exact (hz _).trans (mul_le_mul_of_nonneg_left ((vis_at x x _ (show separation x x+_ ≤4*B from (by rw [separation_self]; omega)) (fun i hi a=>hB.coarse (i,a) hi)).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh) h0)) hr)
      apply hU.trans; unfold fenceCharge; dsimp only; rw [add_mul]; apply le_trans _ (add_le_add hw hz'); convert! dist_triangle (Lq U) (Lq 1) (Cq V) using 1; rw [dist_eq_norm]; rw [dist_comm (Lq _),dist_eq_norm,dist_eq_norm,norm_sub_rev (Lq U),met]; rw [norm_sub_rev (Cq V)] -- order edit
end YM.QCD.Comet
#print axioms YM.QCD.Comet.balance
#print axioms YM.QCD.Comet.load_home
