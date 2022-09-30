<!DOCTYPE html>
<html lang="{{ str_replace('_', '-', app()->getLocale()) }}">
    <head>
        <meta charset="utf-8">
        <meta name="viewport" content="width=device-width, initial-scale=1">

        <title>Alpha Bot Tracker</title>

        <link href="https://fonts.googleapis.com/css?family=Roboto:300,400,500,700&display=swap" rel="stylesheet" />

        <link href="https://use.fontawesome.com/releases/v5.15.1/css/all.css" rel="stylesheet" />

        <link rel="stylesheet" href="{{ asset('css/app.css') }}">

        <!-- Include Frontend Application (webpack mix) -->
        <script defer src="{{asset('js/manifest.js')}}"></script>
        <script defer src="{{asset('js/vendor.js')}}"></script>
        <script defer src="{{asset('js/app.js')}}"></script>
    </head>
    <body>
        <div id="root"></div>
    </body>
</html>
