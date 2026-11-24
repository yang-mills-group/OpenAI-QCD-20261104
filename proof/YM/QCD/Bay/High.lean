import YM.QCD.Bay.Coals
/-! # representation on words. verify saturation-preserving symmetry; proof independent of fresh pack choices -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Metric Set
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Strut LeafM Eyrie Sparks Rudder
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f n: Side} -- fill
variable {j k p:ℕ}{L:Flight j k}{H:f.val=c.val*L.L.val}
local notation "S"=>sliceL L H
variable {A B a b t r q δ κ y x:ℝ} {l:ℕ} {w:Site f}

lemma hidden_p (s: Strut n)(d e:Site n→ℂ)(T W:Spike)(ht:Warrant s d T)(hv:Warrant s e W)(X:Sheet n): aura (haze s T d) X=aura (haze s W e) X:=by
   obtain ⟨c,hc,H⟩:= Strut.faith ht hv
   have hp:haze s T d=c • haze s W e:=by change rides _ (lightP s _ _)= c • rides _ (lightP s W e); rw [ride_smul]; congr; exact funext H
   rw [hp,aura,aura,star_smul,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_comm c,hc,one_smul]
lemma beset (u v : Strut n)(p t:Spike)(d e:Site n→ℂ): haze (pod u v) (t*p) (coin v d e)=haze v p e*haze u t d:=by
 change rides (act _) (lightP (pod u v) _ _)=rides (act v) (lightP v _ _)*rides (act _) (lightP u t d); rw [ride_mul,podA]; exact congr_arg _ (funext (posture d e t p u v))

lemma transferring (b:Bloom k) (x:ℝ)(V:Grid f)(w:Site f)(d:Site f→ℂ)(p:Glare 1 0 0 w d): trackP b x f (pull 1 w V)=aura (hues w 1 d 1) (trackP b x f V):=by
   have hx : quest b 1 1 b.petals (fun _=>1)=b:=by
      cases b with | mk s P F =>
      unfold quest; simp only [Step.rotate_one,List.map_id_fun]; simp [Bloom.mk.injEq, flag, signW,wave_one]
   have hp : trackP b x f V=aura (star _) (trackP b x f (pull 1 w V)):= hx ▸ quest_tag (ξ:=x) w Swing.none p (r:=fun _=>1) (w:=b.petals) (fun i=>⟨by simp,by omega,fun U=>by rw [pull_id,one_smul]⟩) V -- issue
   rw [hp,inverse_aura _ (colour_wheel p Swing.none)]

lemma precious (Z:Offer k a A)(ξ:ℝ)(hp:0<ξ)(he:ξ≤1)(ha:0<a)(v:Strut f)(p:Spike)(u:Site f→ℂ)(ht:Warrant v u p)(W:Grid f):
   wild (frosting Z.W) ξ f (sky v W)= aura (haze v p u) (wild (frosting Z.W) ξ f W):=by
    let H:=wild (frosting Z.W) ξ f
    obtain ⟨d,hd⟩:= shades 1 (0:Site f) 0 v.2
    let t: Strut f:=(1,v.2); let V:Strut f:=(v.1,0)
    have hv : Warrant t d 1:=⟨hd,Swing.none⟩
    have hf:H (sky t W)=aura (haze t 1 d) (H W):=by
       obtain ⟨F,hF⟩:=auraCL (haze t 1 d)
       unfold H wild; rw [← hF,F.map_tsum]; rotate_left; · exact (earns W (coined (a/(1+k)) (by positivity) Z.price (by rw [div_mul_cancel₀ _ (by positivity)])) hp he (by positivity)).of_norm
       refine tsum_congr fun i=> by rw [hF]; exact transferring _ _ _ _ d hd -- syntax
    have hg : Strut.pod t V=v:=by ext1 <;> simp [V,t,pod,affine]
    let e:=ink V; let P:= sat V; have hk:Warrant V e P:= assured _
    have hi := solidly (n:=f) Z.W Z.price hp he ha
    have ht':Warrant (pod t V) u p:=hg.symm ▸ ht
    change H (sky v W)=aura _ (H W); rw [← hg, ←skying, hidden_p (pod t V) u (coin V d e) _ _ ht' (comb hv hk), show H (sky V (sky t W))=aura (haze V P e) (H (sky t W)) from hi.port (sky t W) v.1 e P hk.1 hk.2, hf, combined]; rw [beset]
end YM.QCD.Bay
