import YM.MassiveQCD.Stitch.Uniform
import YM.QCD.Shell.Nil
import YM.MassiveQCD.Plate.Sight

/-! # W-rates at physical N. No ghost opening matrix. Cluster cost for the spun part of a Wound, incl ALL opening tails in retained ops ticket and ALL halo.K.Pin Fest. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Elevator
open Function Lattice Wilson QCD QCD.Creek Grass Ledge Lat Kit Finset NormedSpace RG QCD.Cove QCD.Cove.Send Filter Run Jets
open QCD.Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open QCD.Jets.Sun QCD.Cove.Fj QCD.Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G₀:Flight j k}{h:f.val=c.val*G₀.L.val}
variable {D E J:Type}{μ:D→ℝ}{L:Ratio c f}(G : Send L F D)(P:Rise f F E J)(s:Finset (Fj D E J))(U V:Grid f)
open Spice QCD.Stew Stitch Ribbon
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G₀ h
local notation "Kz"=> coreW G P s
local notation "K'"=> hooks (F:=F) L Kz
local notation "τ"=> rateF c f F x y
local notation "z'"=> Stitch.Tablet.tunnel G s
lemma tunnel_gate (z:Fields f F)(ht:z∈region (limits (coreW G P s))): z' U z ∈ region (limits ((halo G.trim (coreW G P s)).image L.parent)):=by
    refine effects (wipe A B (G.shortP U)) ?_ _ (Stitch.Tablet.lamp G s U z ht); intro i hi; rcases splits_index i with ⟨v,rfl⟩|⟨v,rfl⟩
    · change ha _ _ _ v∈_ at hi; rw [hooked,rootA] at hi; rw [wiper]; refine Subalgebra.sum_mem _ (fun j _=>?_); by_cases hx:G.shortP U v j=0; · rw [hx,zero_smul]; exact Subalgebra.zero_mem _
      apply Subalgebra.smul_mem; apply marked; exact mem_filter.mpr ⟨mem_univ _,mem_image.mpr ⟨_, (Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr hi) (G.sleeps v j U hx)), L.embed_parent _⟩⟩
    change hb _ _ _ v∈_ at hi; rw [hooked,rootB] at hi; rw [tails]; apply marked; exact mem_filter.mpr ⟨mem_univ _,mem_image.mpr ⟨L.embed _,halo_subset _ _ hi,L.embed_parent _⟩⟩
open Ledge
local notation "mz"=> ops s
lemma tokens (hv:0<x)(hy:0<y)(z: Fields f F): load (rateF c f F x y) (near A B z) = load (fun _=>x) z:=by
    let Z:=rateF c f F x y; change load Z (embed (ha c f F) z)=_; rw [transplant (fun i=> rate_ok i hv hy)]; exact congr_arg (fun p=> load p z) (funext fun i=>wagesA B i x y) -- syntax. may unused G:P
lemma tunnel_cap (h:Peak G t x y ξ μ) (hp:Healthy t (brimW G P s) U) (z:Fields f F) (he:z∈region (limits (coreW G P s))):
 load (fun _=>y) (Stitch.Tablet.tunnel G s U z)≤(∏ i∈ops s,μ i)*load (fun _=>x) z:=by
    have hh:Pledge τ (axle G U s) (∏ i∈ops s,μ i):= pledge_spin _ _ _ _ (fun i _=> h.spare i U) _; let X:=near A B z
    exact (ferry (wipe A B (G.shortP U)) (g:=fun _=>y) (fun i=> rate_ok i h.bud h.cup) (ready_tip G P s U h hp) _ (Stitch.Tablet.lamp G s U z he)).trans ((hh.rates X).trans_eq (congr_arg _ (tokens (c:=c) h.bud h.cup z))) -- argument
lemma tunnel_bill (h:Peak G t x y ξ μ) (hh:Healthy t (brimW G P s) U)(hl: Healthy t (brimW G P s) V)(_hx:0≤w)(hA:0≤v)
    (ht: Pledge (rateF c f F x y) (axle G U s - axle G V s) (w*∏ i∈mz,μ i))
    (hp:∀ i∈hooks (F:=F) L (coreW G P s),load (fun _=>y) (wipe A B (G.shortP U) (atom i)-wipe A B (G.shortP V) (atom i)) ≤ v*rateF c f F x y i) (z:Fields f F) (he:z∈region (limits (coreW G P s))):
    load (fun _=>y) (z' U z-z' V z) ≤ (((hooks (F:=F) L (coreW G P s)).card:ℝ)*v+w)*((∏ i∈ops s,μ i)*load (fun _=>x) z):=by
     let T i:=axle G i s (near A B z); let S' i:= wipe A B (G.shortP i); let u:=S' U; let g:=S' V; let a:=rateF c f F x y; let p:=∏ i∈mz,μ i; let l:= load (fun _=>x) z
     have hm q:= Stitch.Tablet.lamp G s q z he; let b (i:Keys c F):=y
     rw [show z' U z-z' V z=(u (T U)-g (T U))+g (T U-T V) from (by change u (T U)- g (T V)=_; rw [map_sub]; abel)]
     have hx' : Pledge a (axle G U s) p:=pledge_spin _ _ _ _ (fun i _=> h.spare i U) _; have hf:= (tokens (c:=c) h.bud h.cup z)
     have hP:load a (T U)≤p*l:=(hx'.rates _).trans_eq (congr_arg _ hf); have hF: load a (T U-T V)≤w*p*l:=(ht.rates (near A B z)).trans_eq (congr_arg _ hf)
     apply (spawnA b _ _).trans; apply (add_le_add ((roughG u g (K') (ready_tip G P s U h hh) (ready_tip G P s V h hl) hp (fun i=> rate_ok i h.bud h.cup) hA _ (hm U)).trans (mul_le_mul_of_nonneg_left hP (mul_nonneg (Nat.cast_nonneg _) hA))) ((ferry g (fun i=>rate_ok i h.bud h.cup) (ready_tip G P s V h hl) _ (Subalgebra.sub_mem _ (hm _) (hm _))).trans hF)).trans_eq; ring
open Cupola Plate QCD.Reggae
lemma shutter (U:Support c)(o:Site c)(m:ℕ)(ht:∀ i∈U,separation i o ≤ m)(x:Fields c F)(hy:0<v)(h:x∈region (limits U)): plank o v x ≤ (1+(m:ℝ))^2*load (fun _=>v) x:=by
    have hx(i:Keys c F)(hi:i∈limits U): Stew.lens o i≤ m:=ht _ (mem_filter.mp hi).2
    apply le_trans (b:=camp (fun _=>v) (Stew.lens o) 2 x) ?_ (camps (fun _=>hy) _ _ _ h _ hx); unfold Stew.plank camp; rw [pricesD _ hy.le]; apply le_of_eq; refine sum_congr rfl fun i _=>?_ ; unfold starch QCD.Cove.weight pieD regionW; simp
open Fj
local notation "P'"=> NormedSpace.exp
lemma nilM {N:ℕ}{I:Type}[Fintype I]{s:Finset I}{q:I→Bool}(x:Tine f N I)(h:Polite q s x)(hf:s.Nonempty): (P') x -1=x:=by
    have hp : x*x=0:= h.nilpotent h (fun h=>Finset.disjoint_left.mp h hf.choose_spec hf.choose_spec) -- rewrite
    apply Subtype.ext; change light _ ((P') x-1)=light _ x; rw [map_sub,map_one, light_exp,radius_two]; abel; rw [← map_mul,hp,map_zero]
    
section data
variable {I:Type}[Fintype I](X: Stitch.Tablet P I){q:I→Bool}{o:I→Site f}(hx:X.Wave t q o){s:Finset (Fj D E J)}{i:E}
local notation "T₀"=> Stitch.Tablet.tunnel G s
noncomputable def tap (i:E):Grid f→ Fields f F:= fun U=> pluck (Keys f F) (burst q (X.spine i)) (X.main i U)
include hx
lemma value (he:leftE s={i})(hS:(X.spine i).Nonempty)(hk:spent s=∅) (hV:Healthy t (brimW G P s) V): X.hue t G s V = X.dye t G s V ∧ ∀ j, pluck (Keys c F) j (X.hue t G s V)= T₀ V (pluck (Keys f F) j (X.main i V)):=by
    have h0:P.wish (spent s)=∅:=by rw [hk]; simp [Rise.wish]; -- indent
    have hh : closeS G P t s V :=by unfold closeS; rw [h0]; unfold Healthy at hV; rw [inter_comm]; exact (disjoint_iff_inter_eq_empty.mp hV).symm
    have he' : X.hue t G s V=X.dye t G s V:=if_pos ⟨(by simp [hk,Rise.spare]),hh⟩
    refine ⟨he',fun j=>?_⟩; have hp: X.read t V i=X.main i V:=masked_eq _ _ _ _ (hV.mono_left (fun j hj=> native_sub G P s (mem_biUnion.mpr ⟨Sum.inr (Sum.inl i),by
                                                                                      have ht : i∈leftE s:=by rw [he]; simp
                                                                                      simpa [leftE] using ht, hj⟩)))
    rw [he']; change scrape (Keys c F) _ (carry _ _ (X.made t V s).val)= _; rw [wing]; unfold Tablet.made; rw [he,hk,prod_singleton,prod_empty,mul_one,hp,nilM _ (hx.showAt i V).1 hS]; rfl -- heartbeat
end data
end YM.MassiveQCD.Elevator
#print axioms YM.MassiveQCD.Elevator.tunnel_cap
#print axioms YM.MassiveQCD.Elevator.value
