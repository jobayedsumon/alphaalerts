<?php

namespace App\Http\Controllers;

use App\Discord;
use App\Models\ChannelNotification;
use App\Models\Project;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Validator;

class ProjectController extends Controller
{
    public function __construct()
    {
        $this->middleware('auth:api');
    }

    public function index()
    {
        $projects = Project::with('channels')->latest()->get();
        return response()->json([
            'status' => 'success',
            'projects' => $projects,
        ]);
    }

    public function store(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'project_name' => 'required|string|max:255',
            'server_id' => 'required|string|max:255|unique:projects',
            'channel_ids' => 'required|string',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => $validator->errors(),
            ]);
        }

        $project = new Project();
        $project->project_name = $request->get('project_name');
        $project->white_label_package = $request->get('white_label_package');
        $project->server_id = $request->get('server_id');
        $project->save();

        $channel_ids = explode(',', $request->get('channel_ids'));

        foreach ($channel_ids as $channel_id) {
            $project->channels()->create([
                'channel_id' => $channel_id,
            ]);
        }

        return response()->json([
            'status' => 'success',
            'project' => $project,
        ]);
    }


    public function show($id)
    {
        $project = Project::with('channels')->findOrFail($id);
        return response()->json([
            'status' => 'success',
            'project' => $project,
        ]);
    }

    public function update(Request $request, Project $project)
    {
        $validator = Validator::make($request->all(), [
            'project_name' => 'required|string|max:255',
            'server_id' => 'required|string|max:255|unique:projects,id,' . $project->id,
            'channel_ids' => 'required|string',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => $validator->errors(),
            ]);
        }

        $project->project_name = $request->get('project_name');
        $project->white_label_package = $request->get('white_label_package');
        $project->server_id = $request->get('server_id');
        $project->save();

        $channel_ids = explode(',', $request->get('channel_ids'));

        $project->channels()->delete();

        foreach ($channel_ids as $channel_id) {
            $project->channels()->create([
                'channel_id' => $channel_id,
            ]);
        }

        return response()->json([
            'status' => 'success',
            'project' => $project,
        ]);
    }

    public function destroy(Project $project)
    {
        $project->delete();
        return response()->json([
            'status' => 'success',
            'message' => 'Project deleted successfully',
        ]);
    }

    public function notification(Request $request) {

        if ($request->get ('notification')) {
            $channel_notification = new ChannelNotification();
            $channel_notification->user_id = Auth::user ()->id;
            $channel_notification->channel_id = $request->get ('channel_id');
            $channel_notification->last_message_id = $request->get ('last_message_id');
            $guild = Discord::guildPreview($request->get ('server_id'));
            $channel_notification->server_name = @$guild->name ?? '';
            $channel_notification->save ();
            return response ()->json ([
                'status' => 'success',
                'notification' => true,
                'message' => 'Notification saved successfully',
            ]);
        } else {
            $channel_notification = ChannelNotification::where('user_id', \auth ()->id ())->where('channel_id', $request->get ('channel_id'))->first();
            if ($channel_notification) {
                $channel_notification->delete ();
            }
            return response ()->json ([
                'status' => 'success',
                'notification' => false,
                'message' => 'Notification deleted successfully',
            ]);
        }
    }
}
